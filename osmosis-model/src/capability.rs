/// MIT License
///
/// Copyright (c) 2025 Ilias Karimalis

use state_machines_macros::*;
use vstd::prelude::*;

use crate::dag::*;

verus!
{

spec const L1_CNODE_INIT_SLOT_CNT: nat = 682;

// ARMv8 specific object sizes:
spec const OBJSIZE_L2CNODE: nat = 16384;
spec const OBJSIZE_DISPATCHER: nat = 1024;

pub type KernelObjectID = usize;

pub ghost struct KernelObjectLocation {
    // Location marked in physical addresses.
    base: nat,
    bytes: nat,
}

pub ghost enum KernelObject {
    L1CNode(Seq<KernelObjectID>),
    L2CNode([KernelObjectID; 256]),
    Dispatcher { cspace: KernelObjectID },
    Capability(Capability),
}


// Constants defining well known Cspace locations:
spec const ROOTCN_SLOT_TASKCN: nat = 0;

pub ghost struct Cap {
    
}

pub ghost enum Capability {
    Null,
    //PhysAddr { base: nat, bytes: nat },
    //DevFrame { base: nat, bytes: nat },
    //RAM { base: nat, bytes: nat  },
    //Frame { base: nat, bytes: nat },
    //Dispatcher,
    L1_CNode { l1_kid: KernelObjectID },
    L2_CNode { l2_kid: KernelObjectID },
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

//pub ghost struct Kernel {
//    
//}

pub spec const U24_MAX: nat = 0x0FFFFFF;

//pub type CapAddr = u32;
pub ghost struct CapAddr {
    pub l1: nat,
    pub l2: u8,
}

impl CapAddr {
    /// A CapAddr is well formed if it can address at most a u32 address space, that is to say l1
    /// must fit in a 24bit unsigned integer.
    pub open spec fn wf(&self, disp: Dispatcher) -> bool {
        // The L1 index must fit into a 24bit value
        &&& 0 <= self.l1 <= U24_MAX
        // and must fall within the bounds of the currently allocated L1CNode
        &&& self.l1 < disp.cspace.len()
    }

    pub open spec fn capability(&self, disp: Dispatcher) -> Capability
        recommends disp.wf() && self.wf(disp)
    {
        disp.cspace.index(self.l1)[self.l2]
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

impl CNodeRef {
    pub open spec fn wf(&self, disp: Dispatcher) -> bool
        recommends
            disp.wf(),
    {
        &&& disp.wf()
        &&& self.root.wf(disp)
        &&& self.node.wf(disp)
        &&& self.root.capability(disp) is L1_CNode
        // Note (2025-04-15)
        // 
        // How do we actually check that the root is the L1CNode root to this CSpace?
        // How does Barrelfish actually check?
        // In reality, this check is performed in the kernel, where the lookup of the CSpace
        // content is not a function of the Dispatcher from which it's called, but rather the work
        // is performed by finding the capability in the mdb.
        &&& false
    }
}

pub ghost struct CapRef {
    /// Identifies where in the calling entities CSpace is the capability to the L1CNode referenced
    /// by this capability reference.
    pub cnode: CNodeRef,
    /// Identifies the offset into the L1CNode in which the referenced capability resides.
    pub addr: CapAddr,
}

impl CapRef {
    /// A CapRef is well formed with respect to a Dispatcher proc iff:
    /// - cnode must reference an existing L1CNode in the disp CSpace
    pub open spec fn wf(&self, disp: Dispatcher) -> bool 
        recommends
            disp.wf(),
    {
        &&& true
         //&&& disp.cspace[cnode.root.l1]
    }

    pub open spec fn capability(&self, disp: Dispatcher) -> Capability
        recommends
            disp.wf() && self.wf(disp),
    {

    }
}

state_machine!
{
    BarrelfishDAGSingleCore {
        spec const NULL_CAP_KERNEL_OBJECT_ID: nat = 0;

        fields {
            /// Maps a pid to its dispatcher
            pub dsps: Map<nat, KernelObjectID>,
            pub kernel_objects: Map<nat, KernelObject>,
        }

        init! {
            initialize()
            {
                let ko = Map::empty();
                ko.insert(NULL_CAP_KERNEL_OBJECT_ID, KernelObject::Capability(Capability::Null));
                init kernel_objects = ko;
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
        transition! {
            cap_copy(entity_pid: nat, dest: CapRef, src: CapRef)
            {
                // The entity must exist
                require pre.dsps.contains(entity_pid);
                let entity_koid = pre.dsps[entity];
                // src must reference a valid capability in the entities CSpace
                require 
                // dst must be a valid empty slot in the destination CSpace
                //require 
                
            }
        }

    }

}


} // verus!


