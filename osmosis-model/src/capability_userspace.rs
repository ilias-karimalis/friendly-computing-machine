// Replicates the Userspace Capability Operations from Barrelfish
//
// This is a direct rewrite of: https://github.com/BarrelfishOS/barrelfish/blob/master/include/barrelfish/caddr.h

use vstd::prelude::verus;

verus! {

pub type CapAddr = u32;
pub type CSlot = u32;

struct CNodeRef {
    croot: CapAddr,
    cnode: CapAddr,
    is_root: bool,
}

impl CNodeRef {
    pub fn is_null(&self) -> bool {
        self.croot == 0 &&  self.cnode == 0
    }

    pub fn cmp(&self, other: CNodeRef) -> bool {
        self.cnode == other.cnode && self.croot == other.croot && self.is_root == other.is_root
    }
}

const NULL_CNODE: CNodeRef = CNodeRef { croot: 0, cnode: 0, is_root: true };

struct CapRef {
    cnode: CNodeRef,
    slot: CSlot,
}

impl CapRef {
    
    pub fn is_null(&self) -> bool {
        self.slot == 0 && self.cnode.is_null() 
    }

    pub fn cmp(&self, other: CapRef) -> bool {
        self.slot == other.slot && self.cnode.cmp(other.cnode)
    }
}

pub fn get_capaddr_slot(addr: CapAddr) -> CSlot {
    addr & (u8::MAX as u32)
}


}
