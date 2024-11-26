use circ_hc::{Node as NodeTrait, Table as TableTrait, generate_hashcons_rc};

generate_hashcons_rc!(u32);

fn main() {
    let node = Table::create(&0, vec![]);
    assert!(node.op() == &0);
}
