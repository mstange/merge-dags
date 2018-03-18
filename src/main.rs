extern crate afl;
extern crate euclid;
extern crate num;

use std::collections::{HashMap, HashSet};
use std::mem;
use num::clamp;

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
pub struct DisplayItemKey {
    frame: usize,
    per_frame_key: usize,
}

pub type Rect = euclid::TypedRect<u32>;

#[derive(Debug, Clone)]
pub struct DisplayItem {
    frame: usize,
    per_frame_key: usize,
    bounds: Rect,
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
pub struct RetainedDisplayList {
    items: Vec<DisplayItem>,
    dag: DirectedAcyclicGraph,
    key_lookup: HashMap<DisplayItemKey, usize>,
}

impl RetainedDisplayList {
    pub fn new() -> RetainedDisplayList {
        RetainedDisplayList {
            items: Vec::new(),
            dag: DirectedAcyclicGraph::new(),
            key_lookup: HashMap::new(),
        }
    }
}

#[derive(Debug)]
enum OldItemInfo {
    Unused(DisplayItem),
    BeingProcessed,
    AddedToMergedList(usize), // index in merged list
    Discarded(Vec<usize>),    // direct predecessors as indexes into merged list
}

impl OldItemInfo {
    fn is_used(&self) -> bool {
        match *self {
            OldItemInfo::Unused(_) => false,
            _ => true,
        }
    }
}

#[derive(Debug)]
struct MergeState<'a> {
    old_items: Vec<OldItemInfo>,
    old_dag: &'a DirectedAcyclicGraph,
    old_key_lookup: HashMap<DisplayItemKey, usize>,
    merged_items: Vec<DisplayItem>,
    merged_dag: DirectedAcyclicGraph,
    merged_key_lookup: HashMap<DisplayItemKey, usize>,
    changed_frames: HashSet<usize>,
}

impl<'a> MergeState<'a> {
    pub fn process_item_from_new_list(
        &mut self,
        new_item: DisplayItem,
        previous_item_index_in_merged_list: Option<usize>,
    ) -> usize {
        if !self.is_changed(&new_item) {
            let key = new_item.provide_key();
            if let Some(&index_in_old_dag) = self.old_key_lookup.get(&key) {
                // This item is already present in the old list.

                assert!(!self.old_items[index_in_old_dag].is_used());
                let direct_predecessors = self.process_predecessors_of_old_node(index_in_old_dag);

                // Add the node to self.merged_dag, possibly with a new edge
                // from previous_item_index_in_merged_list.
                let old_item = mem::replace(
                    &mut self.old_items[index_in_old_dag],
                    OldItemInfo::BeingProcessed,
                );
                // TODO: merge old_item and new_item children
                let index_in_merged_dag = self.add_new_node(
                    new_item,
                    &direct_predecessors,
                    previous_item_index_in_merged_list,
                );
                self.old_items[index_in_old_dag] =
                    OldItemInfo::AddedToMergedList(index_in_merged_dag);
                mem::drop(old_item); // replaced by new_item
                return index_in_merged_dag;
            }
        }
        self.add_new_node(new_item, &[], previous_item_index_in_merged_list)
    }

    pub fn finalize(mut self) -> RetainedDisplayList {
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

        RetainedDisplayList {
            items: self.merged_items,
            dag: self.merged_dag,
            key_lookup: self.merged_key_lookup,
        }
    }

    fn is_changed(&self, item: &DisplayItem) -> bool {
        self.changed_frames.contains(&item.frame)
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
        if let OldItemInfo::Unused(item) =
            mem::replace(&mut self.old_items[node], OldItemInfo::BeingProcessed)
        {
            if self.is_changed(&item) {
                // Discard this node, but store its direct predecessors so that any
                // paths through this node can be preserved.
                self.old_items[node] = OldItemInfo::Discarded(direct_predecessors_in_merged_dag);
            } else {
                // Adopt the node from the old DirectedAcyclicGraph into the new DirectedAcyclicGraph.
                let new_node_index =
                    self.add_new_node(item, &direct_predecessors_in_merged_dag, None);
                self.old_items[node] = OldItemInfo::AddedToMergedList(new_node_index);
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
                &OldItemInfo::Unused(_) => panic!("should only encounter used predecessors"),
                &OldItemInfo::BeingProcessed => panic!("somebody forgot to clean up"),
                &OldItemInfo::Discarded(ref discarded_item_direct_predecessors) => {
                    result.extend(discarded_item_direct_predecessors)
                }
                &OldItemInfo::AddedToMergedList(index_in_merged_dag) => {
                    result.push(index_in_merged_dag)
                }
            }
        }
        result
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
        items,
        dag,
        key_lookup,
    } = old_list;
    let mut merge_state = MergeState {
        old_items: items.into_iter().map(|i| OldItemInfo::Unused(i)).collect(),
        old_dag: &dag,
        old_key_lookup: key_lookup,
        merged_items: Vec::new(),
        merged_dag: DirectedAcyclicGraph::new(),
        merged_key_lookup: HashMap::new(),
        changed_frames,
    };
    let mut previous_item_index = None;
    for new_item in new_list.into_iter() {
        previous_item_index =
            Some(merge_state.process_item_from_new_list(new_item, previous_item_index));
    }

    merge_state.finalize()
}

pub struct TrueDisplayList {
    counter: usize,
    list: Vec<DisplayItem>,
    changed_frames: HashSet<usize>,
}

impl TrueDisplayList {
    pub fn new() -> TrueDisplayList {
        TrueDisplayList {
            counter: 0,
            list: Vec::new(),
            changed_frames: HashSet::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.list.len()
    }

    pub fn add_item(&mut self, bounds: Rect) {
        let index = self.len();
        self.insert_item(index, bounds);
    }

    pub fn insert_item(&mut self, index: usize, bounds: Rect) {
        let frame = self.counter;
        self.counter += 1;
        self.list.insert(
            index,
            DisplayItem {
                frame: frame,
                per_frame_key: frame,
                bounds,
            },
        );
        self.changed_frames.insert(frame);
    }

    pub fn touch_item(&mut self, index: usize) {
        let frame = self.list[index].frame;
        self.changed_frames.insert(frame);
    }

    pub fn resize_item(&mut self, index: usize, new_bounds: Rect) {
        let item = &mut self.list[index];
        item.bounds = new_bounds;
        self.changed_frames.insert(item.frame);
    }

    pub fn reorder_item(&mut self, old_index: usize, new_index: usize) {
        let item = self.list.remove(old_index);
        self.changed_frames.insert(item.frame);
        self.list.insert(new_index, item);
    }

    pub fn delete_item(&mut self, index: usize) {
        let item = self.list.remove(index);
        self.changed_frames.insert(item.frame);
        mem::drop(item);
    }

    pub fn produce_update(&mut self) -> (Vec<DisplayItem>, HashSet<usize>) {
        let mut rebuild_rect = Rect::zero();
        for item in &self.list {
            if self.changed_frames.contains(&item.frame) {
                rebuild_rect = rebuild_rect.union(&item.bounds);
            }
        }
        let mut update_list = Vec::new();
        for item in &self.list {
            if item.bounds.intersects(&rebuild_rect) {
                update_list.push(item.clone());
            }
        }
        let changed_frames = mem::replace(&mut self.changed_frames, HashSet::new());
        (update_list, changed_frames)
    }
}

struct Renderer {
    width: usize,
    height: usize,
}

impl Renderer {
    fn render_list(&self, items: &[DisplayItem]) -> Vec<Option<usize>> {
        let mut pixels = vec![None; self.width * self.height];
        for item in items {
            let bounds = item.bounds;
            for y in bounds.min_y()..bounds.max_y() {
                for x in bounds.min_x()..bounds.max_x() {
                    pixels[self.width * (y as usize) + (x as usize)] = Some(item.frame);
                }
            }
        }
        pixels
    }
}

struct U8Yielder<'a> {
    s: &'a [u8],
}

impl<'a> U8Yielder<'a> {
    fn next(&mut self) -> Option<u8> {
        if self.s.is_empty() {
            return None;
        }
        let b = self.s[0];
        self.s = &self.s[1..];
        Some(b)
    }
}

fn run_test_stream(s: &[u8], width: u8, height: u8) -> Option<()> {
    let mut true_display_list = TrueDisplayList::new();
    let mut retained_display_list = RetainedDisplayList::new();
    let renderer = Renderer {
        width: width as usize,
        height: height as usize,
    };
    let mut s = U8Yielder { s };
    loop {
        match s.next()? {
            1 => {
                // insert item
                if true_display_list.len() < 256 {
                    // shouldn't need more than 255 items to hit interesting cases
                    // println!("insert");
                    let index = clamp(s.next()? as usize, 0, true_display_list.len());
                    let x = clamp(s.next()?, 0, width - 1);
                    let y = clamp(s.next()?, 0, height - 1);
                    let w = clamp(s.next()?, 1, width - x);
                    let h = clamp(s.next()?, 1, height - y);
                    true_display_list
                        .insert_item(index, euclid::rect(x as u32, y as u32, w as u32, h as u32));
                }
            }
            2 => {
                // touch item
                if true_display_list.len() != 0 {
                    // println!("touch");
                    let index = clamp(s.next()? as usize, 0, true_display_list.len() - 1);
                    true_display_list.touch_item(index);
                }
            }
            3 => {
                // reorder item
                if true_display_list.len() != 0 {
                    // println!("reorder");
                    let old_index = clamp(s.next()? as usize, 0, true_display_list.len() - 1);
                    let new_index = clamp(s.next()? as usize, 0, true_display_list.len() - 1);
                    if old_index != new_index {
                        true_display_list.reorder_item(old_index, new_index);
                    }
                }
            }
            4 => {
                // resize item
                if true_display_list.len() != 0 {
                    // println!("resize");
                    let index = clamp(s.next()? as usize, 0, true_display_list.len() - 1);
                    let x = clamp(s.next()?, 0, width - 1);
                    let y = clamp(s.next()?, 0, height - 1);
                    let w = clamp(s.next()?, 1, width - x);
                    let h = clamp(s.next()?, 1, height - y);
                    true_display_list
                        .resize_item(index, euclid::rect(x as u32, y as u32, w as u32, h as u32));
                }
            }
            5 => {
                // delete item
                if true_display_list.len() != 0 {
                    // println!("delete");
                    let index = clamp(s.next()? as usize, 0, true_display_list.len() - 1);
                    true_display_list.delete_item(index);
                }
            }
            _ => {
                // check consistency
                if !true_display_list.changed_frames.is_empty() {
                    let (update_list, changed_frames) = true_display_list.produce_update();
                    // println!("update: {:#?}, {:#?}", update_list, changed_frames);
                    retained_display_list =
                        merge_lists(retained_display_list, update_list, changed_frames);
                    assert_eq!(
                        renderer.render_list(&true_display_list.list),
                        renderer.render_list(&retained_display_list.items)
                    );

                    // println!("merged list: {:#?}", retained_display_list.items);
                }
            }
        }
    }
}

fn main() {
    afl::read_stdio_bytes(|bytes| {
        run_test_stream(&bytes, 32, 32);
    });
}

#[cfg(test)]
mod tests {
    #[test]
    fn insert_between_pancakes() {
        use TrueDisplayList;
        use RetainedDisplayList;
        use Renderer;
        use euclid;
        use merge_lists;

        let mut true_display_list = TrueDisplayList::new();
        let mut retained_display_list = RetainedDisplayList::new();
        let renderer = Renderer {
            width: 32,
            height: 32,
        };

        true_display_list.add_item(euclid::rect(0, 0, 4, 4));
        true_display_list.add_item(euclid::rect(2, 2, 4, 4));
        true_display_list.add_item(euclid::rect(4, 4, 4, 4));
        true_display_list.add_item(euclid::rect(6, 6, 4, 4));
        true_display_list.add_item(euclid::rect(8, 8, 4, 4));

        let (update_list, changed_frames) = true_display_list.produce_update();
        retained_display_list = merge_lists(retained_display_list, update_list, changed_frames);
        assert_eq!(
            renderer.render_list(&true_display_list.list),
            renderer.render_list(&retained_display_list.items)
        );

        true_display_list.add_item(euclid::rect(14, 14, 4, 4));
        true_display_list.add_item(euclid::rect(16, 16, 4, 4));
        true_display_list.add_item(euclid::rect(18, 18, 4, 4));
        true_display_list.add_item(euclid::rect(20, 20, 4, 4));
        true_display_list.add_item(euclid::rect(22, 22, 4, 4));

        let (update_list, changed_frames) = true_display_list.produce_update();
        retained_display_list = merge_lists(retained_display_list, update_list, changed_frames);
        assert_eq!(
            renderer.render_list(&true_display_list.list),
            renderer.render_list(&retained_display_list.items)
        );

        true_display_list.insert_item(5, euclid::rect(10, 10, 6, 6));

        let (update_list, changed_frames) = true_display_list.produce_update();
        println!("update: {:#?}, {:#?}", update_list, changed_frames);
        retained_display_list = merge_lists(retained_display_list, update_list, changed_frames);
        assert_eq!(
            renderer.render_list(&true_display_list.list),
            renderer.render_list(&retained_display_list.items)
        );

        println!("merged list: {:#?}", retained_display_list.items);
    }
}
