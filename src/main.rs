use std::collections::{HashMap, HashSet};
use std::mem;

#[derive(Debug)]
struct NodeInfo {
    index_in_direct_predecessor_list: usize,
    direct_predecessor_count: usize,
}

#[derive(Debug)]
pub struct DirectedAcyclicGraph {
    nodes_info: Vec<NodeInfo>,
    direct_predecessor_list: Vec<usize>,
}

impl DirectedAcyclicGraph {
    pub fn new() -> DirectedAcyclicGraph {
        DirectedAcyclicGraph {
            nodes_info: Vec::new(),
            direct_predecessor_list: Vec::new(),
        }
    }

    /// Create a DirectedAcyclicGraph that has a straight path 0 -> 1 -> ... -> n - 1.
    pub fn new_with_straight_path(n: usize) -> DirectedAcyclicGraph {
        let mut nodes_info = Vec::with_capacity(n);
        let mut direct_predecessor_list = Vec::with_capacity(n - 1);
        if n != 0 {
            nodes_info.push(NodeInfo {
                index_in_direct_predecessor_list: 0,
                direct_predecessor_count: 0,
            });
            for index in 1..n {
                direct_predecessor_list.push(index - 1);
                nodes_info.push(NodeInfo {
                    index_in_direct_predecessor_list: index - 1,
                    direct_predecessor_count: 1,
                });
            }
        }
        DirectedAcyclicGraph {
            nodes_info,
            direct_predecessor_list,
        }
    }

    /// Add a node with the specified direct predecessors. The direct predecessor
    /// nodes are given in terms of indexes into this DAG's node list, so they
    /// need to already be part of this DAG. Consequently, you have to build
    /// this graph up in a topological order and cannot create cycles.
    /// This method will panic if it encounters a direct_predecessor index which
    /// is out of range.
    pub fn add_node(&mut self, direct_predecessors: &[usize]) -> usize {
        let index = self.nodes_info.len();
        self.nodes_info.push(NodeInfo {
            index_in_direct_predecessor_list: self.direct_predecessor_list.len(),
            direct_predecessor_count: direct_predecessors.len(),
        });
        for &direct_predecessor in direct_predecessors {
            assert!(direct_predecessor < index);
        }
        self.direct_predecessor_list.extend(direct_predecessors);
        index
    }

    pub fn len(&self) -> usize {
        self.nodes_info.len()
    }

    pub fn get_direct_predecessors(&self, node_index: usize) -> &[usize] {
        let info = &self.nodes_info[node_index];
        let start_index = info.index_in_direct_predecessor_list;
        let end_index = start_index + info.direct_predecessor_count;
        &self.direct_predecessor_list[start_index..end_index]
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
struct DisplayItemKey {
    frame: usize,
    per_frame_key: usize,
}

#[derive(Debug)]
struct DisplayItem {
    frame: usize,
    per_frame_key: usize,
}

impl DisplayItem {
    fn provide_key(&self) -> DisplayItemKey {
        DisplayItemKey {
            frame: self.frame,
            per_frame_key: self.per_frame_key,
        }
    }
}

#[derive(Debug)]
enum OldNodeInfo {
    Unused(DisplayItem),
    BeingProcessed,
    AddedToMergedDAG(usize), // index in merged DAG
    Discarded(Vec<usize>),   // predecessors as indexes in merged DAG
}

impl OldNodeInfo {
    fn is_used(&self) -> bool {
        match *self {
            OldNodeInfo::Unused(_) => false,
            _ => true,
        }
    }
}

#[derive(Debug)]
struct MergeState<'a> {
    old_dag: &'a DirectedAcyclicGraph,
    old_items: Vec<OldNodeInfo>,
    old_key_lookup: HashMap<DisplayItemKey, usize>,
    merged_dag: DirectedAcyclicGraph,
    merged_items: Vec<DisplayItem>,
    merged_key_lookup: HashMap<DisplayItemKey, usize>,
    changed_frames: HashSet<usize>,
}

impl<'a> MergeState<'a> {
    pub fn key_to_index(&self, key: &DisplayItemKey) -> Option<usize> {
        self.old_key_lookup.get(key).cloned()
    }

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
            if let Some(index_in_old_dag) = self.key_to_index(&key) {
                // This item is already present in the old DirectedAcyclicGraph.

                assert!(!self.old_items[index_in_old_dag].is_used());
                let direct_predecessors = self.process_predecessors_of_old_node(index_in_old_dag);

                // Add the node to self.merged_dag, possibly with a new edge
                // from previous_item_index_in_merged_list.
                let old_item = mem::replace(
                    &mut self.old_items[index_in_old_dag],
                    OldNodeInfo::BeingProcessed,
                );
                // TODO: merge old_item and new_item children
                let index_in_merged_dag = self.add_new_node(
                    new_item,
                    &direct_predecessors,
                    previous_item_index_in_merged_list,
                );
                self.old_items[index_in_old_dag] =
                    OldNodeInfo::AddedToMergedDAG(index_in_merged_dag);
                mem::drop(old_item); // replaced by new_item
                return index_in_merged_dag;
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
        let index = self.merged_dag.len();
        self.merged_key_lookup.insert(item.provide_key(), index);
        self.merged_items.push(item);
        if let Some(extra_direct_predecessor) = extra_direct_predecessor {
            if !direct_predecessors.contains(&extra_direct_predecessor) {
                let mut extended_direct_predecessors =
                    Vec::with_capacity(direct_predecessors.len() + 1);
                extended_direct_predecessors.extend(direct_predecessors);
                extended_direct_predecessors.push(extra_direct_predecessor);
                return self.merged_dag.add_node(&extended_direct_predecessors);
            }
        }
        self.merged_dag.add_node(direct_predecessors)
    }

    fn process_old_node(&mut self, node: usize, direct_predecessors_in_merged_dag: Vec<usize>) {
        if let OldNodeInfo::Unused(item) =
            mem::replace(&mut self.old_items[node], OldNodeInfo::BeingProcessed)
        {
            if self.is_changed(&item) {
                // Discard this node, but store its direct predecessors so that any
                // paths through this node can be preserved.
                self.old_items[node] = OldNodeInfo::Discarded(direct_predecessors_in_merged_dag);
            } else {
                // Adopt the node from the old DirectedAcyclicGraph into the new DirectedAcyclicGraph.
                let new_node_index =
                    self.add_new_node(item, &direct_predecessors_in_merged_dag, None);
                self.old_items[node] = OldNodeInfo::AddedToMergedDAG(new_node_index);
            }
        } else {
            panic!("Shouldn't have used this node yet");
        }
    }

    fn process_predecessors_of_old_node(&mut self, node: usize) -> Vec<usize> {
        let direct_predecessors = self.old_dag.get_direct_predecessors(node);
        for &direct_predecessor in direct_predecessors {
            if self.old_items[direct_predecessor].is_used() {
                // We have processed this node and all its predecessors already.
                continue;
            }
            // Process the predecessors of direct_predecessor first.
            let that_nodes_direct_predecessors_in_merged_dag =
                self.process_predecessors_of_old_node(direct_predecessor);

            // Then process this node itself.
            self.process_old_node(
                direct_predecessor,
                that_nodes_direct_predecessors_in_merged_dag,
            );
        }

        self.resolve_node_indexes_old_to_merged(direct_predecessors)
    }

    fn resolve_node_indexes_old_to_merged(
        &self,
        direct_predecessors_in_old_dag: &[usize],
    ) -> Vec<usize> {
        let mut result = Vec::with_capacity(direct_predecessors_in_old_dag.len());
        for &direct_predecessor in direct_predecessors_in_old_dag {
            match &self.old_items[direct_predecessor] {
                &OldNodeInfo::Unused(_) => panic!("should only encounter used predecessors"),
                &OldNodeInfo::BeingProcessed => panic!("somebody forgot to clean up"),
                &OldNodeInfo::Discarded(ref discarded_item_direct_predecessors) => {
                    result.extend(discarded_item_direct_predecessors)
                }
                &OldNodeInfo::AddedToMergedDAG(index_in_merged_dag) => {
                    result.push(index_in_merged_dag)
                }
            }
        }
        result
    }

    fn finalize(
        mut self,
    ) -> (
        DirectedAcyclicGraph,
        Vec<DisplayItem>,
        HashMap<DisplayItemKey, usize>,
    ) {
        // Iterate over all the remaining unused nodes in self.old_dag and add
        // them to the merged_dag. Then return the merged_dag and consume this
        // object.
        for node in 0..self.old_dag.len() {
            if self.old_items[node].is_used() {
                continue;
            }

            let direct_predecessors =
                self.resolve_node_indexes_old_to_merged(self.old_dag.get_direct_predecessors(node));
            self.process_old_node(node, direct_predecessors);
        }

        // println!("state at the end of finalize: {:#?}", self);

        (self.merged_dag, self.merged_items, self.merged_key_lookup)
    }
}

struct RetainedDisplayList {
    items: Vec<DisplayItem>,
    dag: DirectedAcyclicGraph,
    key_lookup: HashMap<DisplayItemKey, usize>,
}

impl RetainedDisplayList {
    fn new() -> RetainedDisplayList {
        RetainedDisplayList {
            items: Vec::new(),
            dag: DirectedAcyclicGraph::new(),
            key_lookup: HashMap::new(),
        }
    }
}

/// Merge old_list and new_list into a new merged RetainedDisplayList.
/// The DAG contains paths for all known total suborderings of the true display list.
fn merge_lists(
    old_list: RetainedDisplayList,
    new_list: Vec<DisplayItem>,
    changed_frames: HashSet<usize>,
) -> RetainedDisplayList {
    let RetainedDisplayList {
        dag,
        items,
        key_lookup,
    } = old_list;
    let mut merge_state = MergeState {
        old_dag: &dag,
        old_items: items.into_iter().map(|i| OldNodeInfo::Unused(i)).collect(),
        old_key_lookup: key_lookup,
        merged_dag: DirectedAcyclicGraph::new(),
        merged_items: Vec::new(),
        merged_key_lookup: HashMap::new(),
        changed_frames,
    };
    let mut previous_item_index = None;
    for new_item in new_list.into_iter() {
        previous_item_index =
            Some(merge_state.process_item_from_new_list(new_item, previous_item_index));
    }

    let (dag, items, key_lookup) = merge_state.finalize();
    RetainedDisplayList {
        items,
        dag,
        key_lookup,
    }
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
        (0..n).map(|_| self.get_one()).collect()
    }
}

fn main() {
    let mut display_item_generator = DisplayItemGenerator { counter: 0 };
    let merged = merge_lists(
        RetainedDisplayList::new(),
        display_item_generator.get_multiple(5),
        (0..5).collect(),
    );
    let merged = merge_lists(
        merged,
        display_item_generator.get_multiple(4),
        (5..9).collect(),
    );
    println!("merged list: {:#?}", merged.items);
}
