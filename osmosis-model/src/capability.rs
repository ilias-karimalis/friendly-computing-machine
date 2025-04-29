/// MIT License
///
/// Copyright (c) 2025 Ilias Karimalis
use state_machines_macros::*;
use vstd::prelude::*;

use crate::dag::*;

verus! {

spec const L1_CNODE_INIT_SLOT_CNT: nat = 682;

/*****************************************************************************/
// Kernel Specification:
/*****************************************************************************/

// ARMv8 specific object sizes:
spec const OBJSIZE_L2CNODE: nat = 16384;
spec const OBJSIZE_DISPATCHER: nat = 1024;

pub spec const ENTRY_COUNT_L2CNODE: nat = 256;

pub trait KernelObjectIndex {
    spec fn to_obj(&self, state: &KernelState) -> KernelObject
        recommends state.wf();
}

pub type KernelObjectID = usize;

impl KernelObjectIndex for KernelObjectID {
    open spec fn to_obj(&self, state: &KernelState) -> KernelObject
    {
        state.objects.index(*self)
    }
}

pub ghost struct KernelObjectLocation {
    // Location marked in physical addresses.
    base: nat,
    bytes: nat,
}

pub ghost enum KernelObject {
    L1CNode { l1_cnode: L1CNodeObject },
    L2CNode { l2_cnode: L2CNodeObject },
    Dispatcher { disp: DispatcherObject },
    Capability { cap: CapabilityObject },
}

impl KernelObject {
    pub open spec fn wf(&self, state: &KernelState) -> bool {
        match (self) {
            KernelObject::L1CNode { l1_cnode } => l1_cnode.wf(state),
            _ => arbitrary(),
        }
    }
}

pub ghost struct L1CNodeObject {
    pub table: Seq<KernelObjectID>,
}

impl L1CNodeObject {
    pub open spec fn wf(&self, state: &KernelState) -> bool {
        // The Length of the L1CNode must be a multiple of L2 CNode Sizes
        &&& self.table.len() >= ENTRY_COUNT_L2CNODE || self.table.len() % ENTRY_COUNT_L2CNODE == 0
        // The entries of an L1CNode must be well formed capabilities that are either Null or L2CNode
        // capabilities
        &&& forall |kid: KernelObjectID| self.table.contains(kid) ==> {
            &&& state.objects.contains_key(kid)
            &&& state.objects.index(kid) is Capability
            &&& state.objects.index(kid)->cap.wf(state)
            &&& state.objects.index(kid)->cap is Null || state.objects.index(kid)->cap is L2CNode
        }
    }
}

pub ghost struct L2CNodeObject {
    pub table: Seq<KernelObjectID>,
}

impl L2CNodeObject {
    pub open spec fn wf(&self, state: &KernelState) -> bool {
        // The Length of the L2CNode is a fixed size decide by the system architecture
        &&& self.table.len() == ENTRY_COUNT_L2CNODE
        // The entries of an L2Cnode must be valid capabilites
        &&& forall |kid: KernelObjectID| self.table.contains(kid) ==> {
            &&& state.objects.contains_key(kid)
            &&& state.objects.index(kid) is Capability
            &&& state.objects.index(kid)->cap.wf(state)
        }
    }
}

pub ghost struct DispatcherObject {
    pub cspace: KernelObjectID,
}

impl DispatcherObject {
    pub open spec fn wf(&self, state: &KernelState) -> bool {
        // The CSpace of a Dispatcher object must be in the Kernel and well formed
        &&& state.objects.contains_key(self.cspace)
        &&& state.objects.index(self.cspace) is L1CNode
        &&& state.objects.index(self.cspace)->l1_cnode.wf(state)
    }
}

// Constants defining well known Cspace locations:
spec const ROOTCN_SLOT_TASKCN: nat = 0;

pub ghost enum CapabilityObject {
    Null,
    //PhysAddr { base: nat, bytes: nat },
    //DevFrame { base: nat, bytes: nat },
    //RAM { base: nat, bytes: nat  },
    //Frame { base: nat, bytes: nat },
    //Dispatcher,
    L1CNode { l1_kid: KernelObjectID },
    L2CNode { l2_kid: KernelObjectID },
    //IDC_Endpoint,
    //VNode_AARCH64_L0,
    //VNode_AARCH64_L1,
    //VNode_AARCH64_L2,
    //VNode_AARCH64_L3,
    //VNode_AARCH64_L0_Mapping,
    //VNode_AARCH64_L1_Mapping,
    //VNode_AARCH64_L2_Mapping,
    //VNode_AARCH64_L3_Mapping,
}

impl CapabilityObject {
    pub open spec fn wf(&self, state: &KernelState) -> bool {
        true
    }
}

pub ghost struct KernelState {
    pub objects: Map<KernelObjectID, KernelObject>,
}

impl KernelState {
    pub open spec fn wf(&self) -> bool {
        // All Kernel objects must be well formed
        &&& forall |kid: KernelObjectID| self.objects.contains_key(kid) ==> self.objects.index(kid).wf(self)
    }
}



//pub ghost struct Kernel {
//
//}

pub spec const U24_MAX: int = 0x0FFFFFF;
pub spec const U8_MAX: int = 0x0FF;

/*****************************************************************************/
// User Space Specification:
/*****************************************************************************/

pub ghost struct CapAddr {
    pub l1: int,
    pub l2: int,
}

impl CapAddr {
    /// A CapAddr is well formed if it can address at most a u32 address space, that is to say l1
    /// must fit in a 24bit unsigned integer.
    pub open spec fn wf(&self, l1_cnode: L1CNodeObject) -> bool {
        // The L1 index must fit into a 24bit value
        &&& 0 <= self.l1 <= U24_MAX
        // and must fall within the bounds of the currently allocated L1CNode
        &&& self.l1 < l1_cnode.table.len()
        // The L2 index must fir into an 8bit value
        &&& 0 <= self.l2 <= U8_MAX
    }

    pub open spec fn capability(&self, l1_cnode: L1CNodeObject, state: KernelState) -> CapabilityObject
        recommends state.wf() && self.wf(l1_cnode)
    {
        l1_cnode.table.index(self.l1).to_obj(&state)->l2_cnode.table.index(self.l2).to_obj(&state)->cap
        //state.objects.index(l1_cnode.table.index(self.
        //state.objects.index(state.objects.index(l1_cnode.table.index(self.l1))->l2_cnode.table.index(self.l2))->cap
    }
}

pub ghost enum CNodeType {
    L1,
    L2,
}

pub ghost struct CNodeRef {
    /// The location of the Capability to the root L1_CNode of the CSpace of the referencing entity.
    pub root: CapAddr,
    /// The location of the Capability to a CNode in the CSpace of the referencing entity.
    pub node: CapAddr,
    /// The type of CNode being referenced (either L1 or L2).
    pub level: CNodeType,
}

// impl CNodeRef {
//     pub open spec fn wf(&self, disp: DispatcherObject) -> bool
//         recommends
//             disp.wf(),
//     {
//         &&& disp.wf()
//         &&& self.root.wf(disp)
//         &&& self.node.wf(disp)
//         &&& self.root.capability(disp) is L1_CNode
//         // Note (2025-04-15)
//         //
//         // How do we actually check that the root is the L1CNode root to this CSpace?
//         // How does Barrelfish actually check?
//         // In reality, this check is performed in the kernel, where the lookup of the CSpace
//         // content is not a function of the Dispatcher from which it's called, but rather the work
//         // is performed by finding the capability in the mdb.
//         &&& false
//     }
// }

// pub ghost struct CapRef {
//     /// Identifies where in the calling entities CSpace is the capability to the L1CNode referenced
//     /// by this capability reference.
//     pub cnode: CNodeRef,
//     /// Identifies the offset into the L1CNode in which the referenced capability resides.
//     pub addr: CapAddr,
// }

// impl CapRef {
//     /// A CapRef is well formed with respect to a Dispatcher proc iff:
//     /// - cnode must reference an existing L1CNode in the disp CSpace
//     pub open spec fn wf(&self, disp: DispatcherObject) -> bool
//         recommends
//             disp.wf(),
//     {
//         &&& true
//          //&&& disp.cspace[cnode.root.l1]
//     }

//     pub open spec fn capability(&self, disp: DispatcherObject) -> CapabilityObject
//         recommends
//             disp.wf() && self.wf(disp),
//     {

//     }
// }

spec const NULL_CAP_KERNEL_OBJECT_ID: nat = 0;

state_machine!
{
    BarrelfishDAGSingleCore {

        fields {
            pub state: KernelState
        }

        init! {
            initialize()
            {
                init state = KernelState {
                    objects: Map::empty()
                };
            }
        }


        //init! {
        //    initialize(ram_caps: Set<Capability>)
        //    {

        //        let init_process = Process {
        //            // Should we model the early memory of the init process?
        //            vas: Set::empty(),
        //            pmap: Map::empty(),
        //            tables: Set::empty(),
        //            pid: 1,
        //            cspace: Seq::empty(),
        //        };
        //        init procs = Set::empty().insert(init_process);
        //    }
        //}

        /// Copy a capability referenced by src to location dst.
        // transition! {
        //     cap_copy(entity_pid: nat, dest: CapRef, src: CapRef)
        //     {
        //         // The entity must exist
        //         // require pre.dsps.contains(entity_pid);
        //         // let entity_koid = pre.dsps[entity];
        //         // src must reference a valid capability in the entities CSpace
        //         // dst must be a valid empty slot in the destination CSpace
        //         //require

        //     }
        // }
        transition! {
            cap_copy()
            {

            }
        }

    }

}


} // verus!
