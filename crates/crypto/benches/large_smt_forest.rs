//! This module contains the benchmarks for the large SMT forest, focusing on the performance of key
//! operations.

mod common;

use std::hint;

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use miden_crypto::{
    Map,
    merkle::smt::{
        Backend, ForestPersistentBackend, LargeSmtForest, LineageId, PersistentBackendConfig,
        SmtForestUpdateBatch, SmtUpdateBatch, TreeId,
    },
    rand::test_utils::rand_value,
};
use miden_field::Word;

use crate::common::{
    config::{DEFAULT_MEASUREMENT_TIME, DEFAULT_SAMPLE_SIZE},
    data::{
        WordPattern, generate_smt_entries_sequential, generate_test_keys_sequential,
        generate_word_pattern,
    },
};

// CONSTANTS
// ================================================================================================

/// The number of entries to modify in an arbitrary batch of updates.
const BATCH_SIZE: usize = 10_000;

/// The number of trees we update in a single whole-forest batch.
const TREES_PER_BATCH: usize = 50;

/// The number of lineages populated for the multi-tree entries benchmark.
const ENTRIES_BENCHMARK_LINEAGES: usize = 100;

/// The number of versions populated per lineage for the multi-tree entries benchmark.
const ENTRIES_BENCHMARK_VERSIONS: u64 = 100;

// SETUP FUNCTIONALITY
// ================================================================================================

/// The setup for a benchmark over the smt forest.
#[derive(Debug)]
struct ForestSetup<B: Backend> {
    pub forest: LargeSmtForest<B>,
    _file: Option<tempfile::TempDir>,
}
impl ForestSetup<ForestPersistentBackend> {
    /// Sets up a new persistent forest as a benchmark setup.
    fn new_persistent() -> Self {
        let dir = tempfile::tempdir().unwrap();
        let backend =
            ForestPersistentBackend::load(PersistentBackendConfig::new(dir.path()).unwrap())
                .unwrap();
        let forest = LargeSmtForest::new(backend).unwrap();
        let _file = Some(dir);

        Self { forest, _file }
    }
}

/// Generates a tree update batch containing `count` entries which may be additions or removals.
fn generate_tree_update_batch(count: usize) -> SmtUpdateBatch {
    let entries = generate_smt_entries_sequential(count);
    SmtUpdateBatch::from(entries.into_iter())
}

/// Generates a tree update batch with stable keys and values unique to `version`.
///
/// Unlike [`generate_tree_update_batch`], repeated calls to this function produce actual changes
/// to the tree. This makes it suitable for populating multiple versions of a lineage while keeping
/// the number of entries in each version fixed at `count`.
fn generate_tree_update_batch_for_version(count: usize, version: u64) -> SmtUpdateBatch {
    let value_offset = version * count as u64;
    let entries = generate_test_keys_sequential(count).into_iter().enumerate().map(|(i, key)| {
        let value = generate_word_pattern(value_offset + i as u64 + 4, WordPattern::Sequential);
        (key, value)
    });
    SmtUpdateBatch::from(entries)
}

/// Generates a forest update batch containing `count` updates for every provided lineage.
fn generate_forest_update_batch_per_lineage(
    lineages: &[LineageId],
    count: usize,
    version: u64,
) -> SmtForestUpdateBatch {
    let batch = generate_tree_update_batch_for_version(count, version);
    let mut updates = SmtForestUpdateBatch::empty();
    for lineage in lineages {
        *updates.operations(*lineage) = batch.clone();
    }
    updates
}

/// Generates a forest update batch containing `count` entries which may be additions or removals
/// and which are allocated equally over the `lineages` in the forest.
fn generate_forest_update_batch(lineages: &[LineageId], count: usize) -> SmtForestUpdateBatch {
    let mut updates = SmtForestUpdateBatch::empty();
    for lineage in lineages {
        *updates.operations(*lineage) = generate_tree_update_batch(count / lineages.len());
    }
    updates
}

/// Generates `count` lineage identifiers.
fn generate_lineages(count: usize) -> Vec<LineageId> {
    let mut lineages = Vec::new();
    for _ in 0..count {
        lineages.push(LineageId::new(rand_value()));
    }
    lineages
}

// FOREST WITH PERSISTENT BACKEND
// ================================================================================================

// Roughly equivalent to large_smt::large_smt_open in functionality.
benchmark_with_setup_data! {
    large_smt_forest_persistent_open_full_tree,
    DEFAULT_MEASUREMENT_TIME,
    DEFAULT_SAMPLE_SIZE,
    "large_smt_forest_persistent_open_full_tree",
    || {
        let mut setup = ForestSetup::new_persistent();
        let batch = generate_tree_update_batch(BATCH_SIZE);
        let lineage = LineageId::new([0x42; 32]);
        let version = 0;
        setup.forest.add_lineage(lineage, version, batch).unwrap();
        let keys = generate_test_keys_sequential(10);
        let tree = TreeId::new(lineage, version);
        (setup, keys, tree)
    },
    |b: &mut criterion::Bencher, (setup, keys, tree): &(ForestSetup<_>, Vec<Word>, TreeId)| {
        b.iter(|| {
            for key in keys {
                hint::black_box(setup.forest.open(*tree, *key).unwrap());
            }
        })
    }
}

// Doesn't have a direct analogue in large SMT, but should be roughly equivalent in performance to
// large_smt_forest_persistent_open_full_tree above, as the historical portion should not dominate.
benchmark_with_setup_data! {
    large_smt_forest_persistent_open_historical_tree,
    DEFAULT_MEASUREMENT_TIME,
    DEFAULT_SAMPLE_SIZE,
    "large_smt_forest_persistent_open_historical_tree",
    || {
        let mut setup = ForestSetup::new_persistent();
        let initial_batch = generate_tree_update_batch(BATCH_SIZE);
        let lineage = LineageId::new([0x42; 32]);
        let version = 0;
        setup.forest.add_lineage(lineage, version, initial_batch).unwrap();
        let update_batch = generate_tree_update_batch(BATCH_SIZE);
        setup.forest.update_tree(lineage, 1, update_batch).unwrap();

        let keys = generate_test_keys_sequential(10);
        let tree = TreeId::new(lineage, version);
        (setup, keys, tree)
    },
    |b: &mut criterion::Bencher, (setup, keys, tree): &(ForestSetup<_>, Vec<Word>, TreeId)| {
        b.iter(|| {
            for key in keys {
                hint::black_box(setup.forest.open(*tree, *key).unwrap());
            }
        })
    },
}

// Measures iteration over the latest version of a tree (the WithoutHistory fast path).
benchmark_with_setup_data! {
    large_smt_forest_persistent_entries_current_tree,
    DEFAULT_MEASUREMENT_TIME,
    DEFAULT_SAMPLE_SIZE,
    "large_smt_forest_persistent_entries_current_tree",
    || {
        let mut setup = ForestSetup::new_persistent();
        let batch = generate_tree_update_batch(BATCH_SIZE);
        let lineage = LineageId::new([0x42; 32]);
        let version = 0;
        setup.forest.add_lineage(lineage, version, batch).unwrap();
        let tree = TreeId::new(lineage, version);
        (setup, tree)
    },
    |b: &mut criterion::Bencher, (setup, tree): &(ForestSetup<_>, TreeId)| {
        b.iter(|| {
            hint::black_box(
                setup.forest.entries(*tree).unwrap().map(|e| e.unwrap()).collect::<Vec<_>>()
            );
        })
    }
}

// Measures iteration over the latest version of a tree in a forest populated with multiple
// lineages and multiple versions per lineage. Every version applies BATCH_SIZE updates while
// retaining BATCH_SIZE entries in the tree.
benchmark_with_setup_data! {
    large_smt_forest_persistent_entries_current_tree_populated_forest,
    DEFAULT_MEASUREMENT_TIME,
    DEFAULT_SAMPLE_SIZE,
    "large_smt_forest_persistent_entries_current_tree_populated_forest",
    || {
        let mut setup = ForestSetup::new_persistent();
        let lineages = generate_lineages(ENTRIES_BENCHMARK_LINEAGES);

        let initial_batch = generate_forest_update_batch_per_lineage(&lineages, BATCH_SIZE, 0);
        setup.forest.add_lineages(0, initial_batch).unwrap();

        for version in 1..ENTRIES_BENCHMARK_VERSIONS {
            let batch = generate_forest_update_batch_per_lineage(&lineages, BATCH_SIZE, version);
            setup.forest.update_forest(version, batch).unwrap();
        }

        let tree = TreeId::new(lineages[0], ENTRIES_BENCHMARK_VERSIONS - 1);
        (setup, tree)
    },
    |b: &mut criterion::Bencher, (setup, tree): &(ForestSetup<_>, TreeId)| {
        b.iter(|| {
            hint::black_box(
                setup.forest.entries(*tree).unwrap().map(|e| e.unwrap()).collect::<Vec<_>>()
            );
        })
    }
}

// Measures iteration over a historical version of a tree (the WithHistory state machine path).
benchmark_with_setup_data! {
    large_smt_forest_persistent_entries_historical_tree,
    DEFAULT_MEASUREMENT_TIME,
    DEFAULT_SAMPLE_SIZE,
    "large_smt_forest_persistent_entries_historical_tree",
    || {
        let mut setup = ForestSetup::new_persistent();
        let initial_batch = generate_tree_update_batch(BATCH_SIZE);
        let lineage = LineageId::new([0x42; 32]);
        let version = 0;
        setup.forest.add_lineage(lineage, version, initial_batch).unwrap();
        let update_batch = generate_tree_update_batch(BATCH_SIZE);
        setup.forest.update_tree(lineage, version + 1, update_batch).unwrap();
        let tree = TreeId::new(lineage, version);
        (setup, tree)
    },
    |b: &mut criterion::Bencher, (setup, tree): &(ForestSetup<_>, TreeId)| {
        b.iter(|| {
            hint::black_box(
                setup.forest.entries(*tree).unwrap().map(|e| e.unwrap()).collect::<Vec<_>>()
            );
        })
    },
}

// Roughly equivalent to large_smt::large_smt_get in functionality.
benchmark_with_setup_data! {
    large_smt_forest_persistent_get_full_tree,
    DEFAULT_MEASUREMENT_TIME,
    DEFAULT_SAMPLE_SIZE,
    "large_smt_forest_persistent_get_full_tree",
    || {
        let mut setup = ForestSetup::new_persistent();
        let batch = generate_tree_update_batch(BATCH_SIZE);
        let lineage = LineageId::new([0x42; 32]);
        let version = 0;
        setup.forest.add_lineage(lineage, version, batch).unwrap();
        let keys = generate_test_keys_sequential(10);
        let tree = TreeId::new(lineage, version);
        (setup, keys, tree)
    },
    |b: &mut criterion::Bencher, (setup, keys, tree): &(ForestSetup<_>, Vec<Word>, TreeId)| {
        b.iter(|| {
            for key in keys {
                hint::black_box(setup.forest.get(*tree, *key).unwrap());
            }
        })
    }
}

// Benchmarks `get` on a historical tree version.
benchmark_with_setup_data! {
    large_smt_forest_persistent_get_historical_tree,
    DEFAULT_MEASUREMENT_TIME,
    DEFAULT_SAMPLE_SIZE,
    "large_smt_forest_persistent_get_historical_tree",
    || {
        let mut setup = ForestSetup::new_persistent();
        let initial_batch = generate_tree_update_batch(BATCH_SIZE);
        let lineage = LineageId::new([0x42; 32]);
        let version = 0;
        setup.forest.add_lineage(lineage, version, initial_batch).unwrap();
        let update_batch = generate_tree_update_batch(BATCH_SIZE);
        setup.forest.update_tree(lineage, 1, update_batch).unwrap();

        let keys = generate_test_keys_sequential(10);
        let tree = TreeId::new(lineage, version);
        (setup, keys, tree)
    },
    |b: &mut criterion::Bencher, (setup, keys, tree): &(ForestSetup<_>, Vec<Word>, TreeId)| {
        b.iter(|| {
            for key in keys {
                hint::black_box(setup.forest.get(*tree, *key).unwrap());
            }
        })
    },
}

// Measures `entry_count` on the latest version of a tree.
benchmark_with_setup_data! {
    large_smt_forest_persistent_entry_count_current_tree,
    DEFAULT_MEASUREMENT_TIME,
    DEFAULT_SAMPLE_SIZE,
    "large_smt_forest_persistent_entry_count_current_tree",
    || {
        let mut setup = ForestSetup::new_persistent();
        let batch = generate_tree_update_batch(BATCH_SIZE);
        let lineage = LineageId::new([0x42; 32]);
        let version = 0;
        setup.forest.add_lineage(lineage, version, batch).unwrap();
        let tree = TreeId::new(lineage, version);
        (setup, tree)
    },
    |b: &mut criterion::Bencher, (setup, tree): &(ForestSetup<_>, TreeId)| {
        b.iter(|| {
            hint::black_box(setup.forest.entry_count(*tree).unwrap());
        })
    }
}

// Measures `entry_count` on a historical version of a tree.
benchmark_with_setup_data! {
    large_smt_forest_persistent_entry_count_historical_tree,
    DEFAULT_MEASUREMENT_TIME,
    DEFAULT_SAMPLE_SIZE,
    "large_smt_forest_persistent_entry_count_historical_tree",
    || {
        let mut setup = ForestSetup::new_persistent();
        let initial_batch = generate_tree_update_batch(BATCH_SIZE);
        let lineage = LineageId::new([0x42; 32]);
        let version = 0;
        setup.forest.add_lineage(lineage, version, initial_batch).unwrap();
        let update_batch = generate_tree_update_batch(BATCH_SIZE);
        setup.forest.update_tree(lineage, version + 1, update_batch).unwrap();
        let tree = TreeId::new(lineage, version);
        (setup, tree)
    },
    |b: &mut criterion::Bencher, (setup, tree): &(ForestSetup<_>, TreeId)| {
        b.iter(|| {
            hint::black_box(setup.forest.entry_count(*tree).unwrap());
        })
    },
}

// Roughly equivalent to large_smt::large_smt_insert_batch_to_empty_tree in functionality.
benchmark_batch! {
    large_smt_forest_persistent_add_lineage,
    &[100, 1_000, 10_000],
    |b: &mut criterion::Bencher, entry_count: usize| {
        let lineage = LineageId::new([0x42; 32]);
        let version = 0;

        b.iter_batched(
            || {
                let batch = generate_tree_update_batch(entry_count);
                let setup = ForestSetup::new_persistent();
                (setup, batch)
            },
            |(mut setup, batch)| {
                setup.forest.add_lineage(lineage, version, batch).unwrap()
            },
            BatchSize::LargeInput
        )
    },
    |size| Some(criterion::Throughput::Elements(size as u64))
}

// Roughly equivalent to large_smt::large_smt_insert_batch_to_populated_tree in functionality.
benchmark_batch! {
    large_smt_forest_persistent_update_tree,
    &[100, 1_000, 10_000],
    |b: &mut criterion::Bencher, entry_count: usize| {
        let initial_batch = generate_tree_update_batch(BATCH_SIZE);
        let lineage = LineageId::new([0x42; 32]);
        let version = 0;

        b.iter_batched(
            || {
                let mut setup = ForestSetup::new_persistent();
                setup.forest.add_lineage(lineage, version, initial_batch.clone()).unwrap();
                let batch = generate_tree_update_batch(entry_count);
                (setup, batch)
            },
            |(mut setup, batch)| {
                setup.forest.update_tree(lineage, version + 1, batch).unwrap();
            },
            BatchSize::LargeInput
        )
    },
    |size| Some(criterion::Throughput::Elements(size as u64))
}

// Benchmarks the addition of multiple lineages in a single batch through repeated calls to
// `add_lineage` and thereby provides a point of comparison for the actual parallel `add_lineage`
// implementation.
benchmark_batch! {
    large_smt_forest_persistent_add_lineages_sequential,
    &[10, 100, 1000],
    |b: &mut criterion::Bencher, lineage_count: usize| {
        let lineages = generate_lineages(lineage_count);

        b.iter_batched(
            || {
                let setup = ForestSetup::new_persistent();
                let batch = generate_forest_update_batch(&lineages, BATCH_SIZE)
                    .consume()
                    .into_iter()
                    .map(|(l, b)| (l, SmtUpdateBatch::new(b.into_iter())))
                    .collect::<Map<_, _>>();
                (setup, batch)
            },
            |(mut setup, batches)| {
                for (lineage, batch) in batches {
                    hint::black_box(setup.forest.add_lineage(lineage, 0, batch).unwrap());
                }
            },
            BatchSize::LargeInput
        )
    },
    |size| Some(criterion::Throughput::Elements(size as u64))
}

// Benchmarks the addition of multiple lineages in a single batch.
benchmark_batch! {
    large_smt_forest_persistent_add_lineages,
    &[10, 100, 1000],
    |b: &mut criterion::Bencher, lineage_count: usize| {
        let lineages = generate_lineages(lineage_count);

        b.iter_batched(
            || {
                let setup = ForestSetup::new_persistent();
                let batch = generate_forest_update_batch(&lineages, BATCH_SIZE);
                (setup, batch)
            },
            |(mut setup, batch)| {
                hint::black_box(setup.forest.add_lineages(0, batch).unwrap())
            },
            BatchSize::LargeInput
        )
    },
    |size| Some(criterion::Throughput::Elements(size as u64))
}

// Has no direct equivalent in the large smt, but should be broadly equivalent work-wise to the
// large_smt_forest_persistent_update_tree above in time as we try and do as much in parallel as
// possible.
benchmark_batch! {
    large_smt_forest_persistent_update_forest,
    &[100, 1_000, 10_000],
    |b: &mut criterion::Bencher, entry_count: usize| {
        let initial_batch = generate_tree_update_batch(100);
        let lineages = generate_lineages(TREES_PER_BATCH);

        b.iter_batched(
            || {
                let mut setup = ForestSetup::new_persistent();
                let version = 0;
                for lineage in &lineages {
                    setup.forest.add_lineage(*lineage, version, initial_batch.clone()).unwrap();
                }

                let batch = generate_forest_update_batch(&lineages, entry_count);

                (setup, batch)
            },
            |(mut setup, batch)| {
                hint::black_box(setup.forest.update_forest(1, batch).unwrap())
            },
            BatchSize::LargeInput
        )
    },
    |size| Some(criterion::Throughput::Elements(size as u64))
}

// BENCHMARK RUNS
// ================================================================================================

criterion_group!(
    large_smt_forest_persistent_group,
    large_smt_forest_persistent_open_full_tree,
    large_smt_forest_persistent_open_historical_tree,
    large_smt_forest_persistent_get_full_tree,
    large_smt_forest_persistent_get_historical_tree,
    large_smt_forest_persistent_entry_count_current_tree,
    large_smt_forest_persistent_entry_count_historical_tree,
    large_smt_forest_persistent_entries_current_tree,
    large_smt_forest_persistent_entries_current_tree_populated_forest,
    large_smt_forest_persistent_entries_historical_tree,
    large_smt_forest_persistent_add_lineage,
    large_smt_forest_persistent_add_lineages_sequential,
    large_smt_forest_persistent_add_lineages,
    large_smt_forest_persistent_update_tree,
    large_smt_forest_persistent_update_forest,
);

criterion_main!(large_smt_forest_persistent_group);
