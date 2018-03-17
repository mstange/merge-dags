use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::slice;
use std::iter;

pub trait ProvidesKey<K>
where
    K: Hash + Eq,
{
    fn provide_key(&self) -> K;
}

#[derive(Debug)]
struct NodeInfo {
    index_in_direct_predecessor_list: usize,
    direct_predecessor_count: usize,
}

#[derive(Debug)]
pub struct DAG<K, V>
where
    K: Hash + Eq,
    V: ProvidesKey<K>,
{
    nodes: Vec<V>,
    nodes_info: Vec<NodeInfo>,
    direct_predecessor_list: Vec<usize>,
    map: HashMap<K, usize>,
}

impl<K, V> DAG<K, V>
where
    K: Hash + Eq,
    V: ProvidesKey<K>,
{
    pub fn new() -> DAG<K, V> {
        DAG {
            nodes: Vec::new(),
            nodes_info: Vec::new(),
            direct_predecessor_list: Vec::new(),
            map: HashMap::new(),
        }
    }

    // Create a DAG that has a straight path nodes[0] -> nodes[1] -> ... -> nodes[n - 1].
    pub fn from_path(nodes: Vec<V>) -> DAG<K, V> {
        let mut nodes_info = Vec::new();
        let mut map = HashMap::new();
        let mut direct_predecessor_list = Vec::with_capacity(nodes.len() - 1);
        if !nodes.is_empty() {
            map.insert(nodes[0].provide_key(), 0);
            nodes_info.push(NodeInfo {
                index_in_direct_predecessor_list: 0,
                direct_predecessor_count: 0,
            });
            for index in 1..nodes.len() {
                direct_predecessor_list.push(index - 1);
                map.insert(nodes[index].provide_key(), index);
                nodes_info.push(NodeInfo {
                    index_in_direct_predecessor_list: index - 1,
                    direct_predecessor_count: 1,
                });
            }
        }
        DAG {
            nodes,
            nodes_info,
            direct_predecessor_list,
            map,
        }
    }

    /// Add a node with the specified direct predecessors. The direct predecessor
    /// nodes are given in terms of indexes into this DAG's node list, so they
    /// need to already be part of this DAG. Consequently, you have to build
    /// this graph up in a topological order and cannot create cycles.
    /// This method will panic if it encounters a direct_predecessor index which
    /// is out of range.
    pub fn add_node(&mut self, node: V, direct_predecessors: &[usize]) -> usize {
        let index = self.nodes.len();
        self.map.insert(node.provide_key(), index);
        self.nodes.push(node);
        self.nodes_info.push(NodeInfo {
            index_in_direct_predecessor_list: self.direct_predecessor_list.len(),
            direct_predecessor_count: direct_predecessors.len(),
        });
        self.direct_predecessor_list.extend(direct_predecessors);
        index
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn key_to_index(&self, key: &K) -> Option<usize> {
        self.map.get(key).cloned()
    }

    pub fn get_direct_predecessors(&self, node_index: usize) -> &[usize] {
        let info = &self.nodes_info[node_index];
        let start_index = info.index_in_direct_predecessor_list;
        let end_index = start_index + info.direct_predecessor_count;
        &self.direct_predecessor_list[start_index..end_index]
    }

    pub fn iter_in_topological_order(&self) -> slice::Iter<V> {
        // Our nodes vector is already a topological order.
        self.nodes.iter()
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
struct DisplayItemKey {
    frame: usize,
    per_frame_key: usize,
}

#[derive(Clone, Debug)]
struct DisplayItem {
    frame: usize,
    per_frame_key: usize,
}

impl ProvidesKey<DisplayItemKey> for DisplayItem {
    fn provide_key(&self) -> DisplayItemKey {
        DisplayItemKey {
            frame: self.frame,
            per_frame_key: self.per_frame_key,
        }
    }
}

#[derive(Debug)]
struct MergeState<'a> {
    old_dag: &'a DAG<DisplayItemKey, DisplayItem>,
    merged_dag: DAG<DisplayItemKey, DisplayItem>,
    changed_frames: HashSet<usize>,
    used: Vec<bool>,
    destroyed_items_direct_predecessors: Vec<Option<Vec<usize>>>,
}

impl<'a> MergeState<'a> {
    fn is_changed(&self, item: &DisplayItem) -> bool {
        self.changed_frames.contains(&item.frame)
    }
    fn process_item_from_new_list(
        &mut self,
        new_item: DisplayItem,
        previous_item_index_in_merged_list: Option<usize>,
    ) -> usize {
        if !self.is_changed(&new_item) {
            let key = new_item.provide_key();
            if let Some(index_in_old_dag) = self.old_dag.key_to_index(&key) {
                // This item is already present in the old DAG.

                assert!(!self.used[index_in_old_dag]);
                let direct_predecessors = self.process_predecessors_of_old_node(index_in_old_dag);
                // Add the node to self.merged_dag, possibly with a new edge
                // from previous_item_index_in_merged_list.
                return self.add_new_node(
                    new_item,
                    &direct_predecessors,
                    previous_item_index_in_merged_list,
                );
            }
        }
        self.add_new_node(new_item, &[], previous_item_index_in_merged_list)
    }

    /// Adds a new node and returns its index.
    fn add_new_node(
        &mut self,
        item: DisplayItem,
        direct_predecessors: &[usize],
        extra_direct_predecessor: Option<usize>,
    ) -> usize {
        if let Some(extra_direct_predecessor) = extra_direct_predecessor {
            if !direct_predecessors.contains(&extra_direct_predecessor) {
                let mut extended_direct_predecessors =
                    Vec::with_capacity(direct_predecessors.len() + 1);
                extended_direct_predecessors.extend(direct_predecessors);
                extended_direct_predecessors.push(extra_direct_predecessor);
                return self.merged_dag
                    .add_node(item, &extended_direct_predecessors);
            }
        }
        self.merged_dag.add_node(item, direct_predecessors)
    }

    fn process_old_node(&mut self, node: usize, direct_predecessors: Vec<usize>) {
        if self.is_changed(&self.old_dag.nodes[node]) {
            // Discard this node, but store its direct predecessors so that any
            // paths through this node can be preserved.
            self.destroyed_items_direct_predecessors[node] = Some(direct_predecessors);
        } else {
            // Adopt the node from the old DAG into the new DAG.
            self.add_new_node(self.old_dag.nodes[node].clone(), &direct_predecessors, None);
        }
        assert!(!self.used[node]);
        self.used[node] = true;
    }

    fn process_predecessors_of_old_node(&mut self, node: usize) -> Vec<usize> {
        let direct_predecessors = self.old_dag.get_direct_predecessors(node);
        for &direct_predecessor in direct_predecessors {
            if self.used[direct_predecessor] {
                // We have processed this node and all its predecessors already.
                continue;
            }
            // Process the predecessors of direct_predecessor first.
            let that_nodes_direct_predecessors =
                self.process_predecessors_of_old_node(direct_predecessor);

            // Then process this node itself.
            self.process_old_node(direct_predecessor, that_nodes_direct_predecessors);
        }

        self.resolve_direct_predecessors_across_destroyed_items(direct_predecessors)
    }

    fn resolve_direct_predecessors_across_destroyed_items(
        &self,
        direct_predecessors: &[usize],
    ) -> Vec<usize> {
        let mut result = Vec::new();
        for &direct_predecessor in direct_predecessors {
            if let Some(destroyed_items_direct_predecessors) =
                self.destroyed_items_direct_predecessors[direct_predecessor].as_ref()
            {
                result.extend(destroyed_items_direct_predecessors);
            } else {
                result.push(direct_predecessor);
            }
        }
        result
    }

    fn finalize(mut self) -> DAG<DisplayItemKey, DisplayItem> {
        // Iterate over all the remaining unused nodes in self.old_dag and add
        // them to the merged_dag. Then return the merged_dag and consume this
        // object.
        for node in 0..self.old_dag.len() {
            if self.used[node] {
                continue;
            }

            let direct_predecessors = self.resolve_direct_predecessors_across_destroyed_items(
                self.old_dag.get_direct_predecessors(node),
            );
            self.process_old_node(node, direct_predecessors);
        }

        // println!("state at the end of finalize: {:#?}", self);

        self.merged_dag
    }
}

/// Merge old_dag and new_list into a new merged DAG.
/// The DAG contains paths for all known total suborderings of the true display list.
fn merge_lists(
    old_dag: DAG<DisplayItemKey, DisplayItem>,
    new_list: Vec<DisplayItem>,
    changed_frames: HashSet<usize>
) -> DAG<DisplayItemKey, DisplayItem> {
    let mut merge_state = MergeState {
        old_dag: &old_dag,
        merged_dag: DAG::new(),
        changed_frames,
        used: vec![false; old_dag.len()],
        destroyed_items_direct_predecessors: vec![None; old_dag.len()],
    };
    let mut previous_item_index = None;
    for new_item in new_list.into_iter() {
        previous_item_index =
            Some(merge_state.process_item_from_new_list(new_item, previous_item_index));
    }

    merge_state.finalize()
}

struct DisplayItemGenerator {
    counter: usize,
}

impl DisplayItemGenerator {
    fn get_one(&mut self) -> DisplayItem {
        let item = DisplayItem {
            frame: self.counter,
            per_frame_key: self.counter,
        };
        self.counter += 1;
        item
    }

    fn get_multiple(&mut self, n: usize) -> Vec<DisplayItem> {
        iter::repeat(()).take(n).map(|_| self.get_one()).collect()
    }
}

fn main() {
    let mut display_item_generator = DisplayItemGenerator { counter: 0 };
    let merged = merge_lists(DAG::new(), display_item_generator.get_multiple(5), (0..5).collect());
    let merged = merge_lists(merged, display_item_generator.get_multiple(4), (5..9).collect());
    println!("merged list: {:#?}", merged.iter_in_topological_order());
}
