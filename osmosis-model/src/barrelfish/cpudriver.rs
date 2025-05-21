/// MIT License
///
/// Copyright (c) 2025 Ilias Karimalis

use state_machines_macros::*;
use vstd::prelude::*;

use crate::utils::Optional;
use crate::barrelfish::kpi::{CapAddr, CapSlot};

verus! {

    // We model kernel resources as a disjoint set of kernel objects. These objects must satisfy
    // the various capability constsraints detailed in the Barrelfishs capability spec.

    /// A Unique indetifier for an existing kernel object.
    pub type KernelObjectID = nat;
    
    ///////////////////////////////////////////////////////////////////////////
    // Capability Type
    ///////////////////////////////////////////////////////////////////////////

    /// A Capability is for the most part, a pointer to another existing kernel object.
    pub ghost enum CapabilityObject {
        Null,
        L1CNode { l1_kid: KernelObjectID },
        L2CNode { l2_kid: KernelObjectID },
    }

    impl CapabilityObject {
        pub open spec fn wf(self, state: &CpuDriverState) -> bool {
            // TODO(Ilias: Every capability object has to point to the correct type of object, and
            //             each of those has to be well formed).
            match (self) {
                CapabilityObject::Null => true,
                // The well formedness of the underlying object is going to be checked by the
                // CpuDriverState wf check and does not need to be checked here.
                CapabilityObject::L1CNode { l1_kid } => state.l1_cnodes.contains_key(l1_kid), // && state.l1_cnodes.index(l1_kid).wf(state),
                CapabilityObject::L2CNode { l2_kid } => state.l2_cnodes.contains_key(l2_kid), // && state.l2_cnodes.index(l2_kid).wf(state),
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // L1 CNode Type
    ///////////////////////////////////////////////////////////////////////////

    /// The model representation of an L1 CNode.
    pub ghost struct L1CNodeObject {
        pub table: Seq<KernelObjectID>,
    }

    impl L1CNodeObject {
        pub open spec fn wf(&self, state: &CpuDriverState) -> bool {
            // The Length of an L1 Cnode must be a multiple of L2 CNode Sizes
            &&& self.table.len() >= ENTRY_COUNT_L1CNODE || self.table.len() % ENTRY_COUNT_L1CNODE == 0
            // The entries of an L1CNode must all be well formed capabilites that are either Null
            // or L2CNode capabilities.
            &&& forall |kid: KernelObjectID| self.table.contains(kid) ==> {
                &&& state.capabilities.contains_key(kid)
                &&& state.capabilities.index(kid) is Null || state.capabilities.index(kid) is L2CNode
                // The well formedness of the underlying capability is going to be checked by the
                // CpuDriverState wf check and does not need to be checked here.
                // &&& state.capabilities.index(kid).wf(state)
            }
        }

        // Checks that the CapAddr is a well formed access into this L1 Cnode
        pub open spec fn wf_access(&self, addr: CapAddr) -> bool {
            &&& addr.wf()
            &&& self.table.len() > addr.l1
        }

        // Accesses the L1CNode and returns the L2CNode entry if one exists
        pub open spec fn index(&self, addr: CapAddr, state: &CpuDriverState) -> Optional<L2CNodeObject>
            recommends state.wf() && self.wf_access(addr)
        {
            let cap: CapabilityObject = state.capabilities.index(self.table.index(addr.l1));
            if (cap is L2CNode) {
                Optional::Some { some: state.l2_cnodes.index(cap->l2_kid) }
            } else {
                Optional::None
            }
        }
    }
    
    ///////////////////////////////////////////////////////////////////////////
    // L2 CNode Type
    ///////////////////////////////////////////////////////////////////////////

    /// The model representation of an L2 CNode.
    pub ghost struct L2CNodeObject {
        pub table: Seq<KernelObjectID>,
    }

    impl L2CNodeObject {
        pub open spec fn wf(&self, state: &CpuDriverState) -> bool {
            // The length of an L2 CNode is the fixed size decided by the system architecture
            &&& self.table.len() == ENTRY_COUNT_L2CNODE
            // The entries of an L2CNode must all be valid capabilites
            &&& forall |kid: KernelObjectID| self.table.contains(kid) ==> {
                &&& state.capabilities.contains_key(kid)
                // The well formedness of the underlying capability is going to be checked by the
                // CpuDriverState wf check and does not need to be checked here.
                // &&& state.capabilities.index(kid).wf(state)
            }
        }

        // Checks that CapSlot is a well formed access into this L2 Cnode
        pub open spec fn wf_access(&self, slot: CapSlot) -> bool {
            &&& slot.wf()
            &&& self.table.len() > slot.idx
        }

        // Accesses the L2CNode and returns the Capability that resides in that slot
        pub open spec fn index(&self, slot: CapSlot, state: &CpuDriverState) -> CapabilityObject
            recommends state.wf() && self.wf(state) && self.wf_access(slot)
        {
            state.capabilities.index(self.table.index(slot.idx))
        }
    }
    
    ///////////////////////////////////////////////////////////////////////////
    // Dispatcher State:
    ///////////////////////////////////////////////////////////////////////////
    
    /// The model representation of a Dispatcher.
    pub ghost struct Dispatcher {
        /// The ID of the L1 CNode Object for this dispatcher.
        pub cspace: KernelObjectID, 
    }

    impl Dispatcher {
        pub open spec fn wf(&self, state: &CpuDriverState) -> bool {
            // The cspace of a dispatcher object must be in the kernel and well formed
            &&& state.l1_cnodes.contains_key(self.cspace)
            // TODO we could make wf a proper recursive wf() condition and check it here.
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // CPU Driver State:
    ///////////////////////////////////////////////////////////////////////////

    /// A representation of a barrelfish cpu driver state.
    pub ghost struct CpuDriverState {
        /// The set of valid capabilities
        pub capabilities: Map<KernelObjectID, CapabilityObject>,
        /// The set of valid L1 CNodes
        pub l1_cnodes: Map<KernelObjectID, L1CNodeObject>,
        /// The set of valid L2 CNodes
        pub l2_cnodes: Map<KernelObjectID, L2CNodeObject>,
        /// The set of dispatchers 
        pub disps: Map<KernelObjectID, Dispatcher>
    }

    impl CpuDriverState {
        pub open spec fn wf(&self) -> bool {
            /// All Kernel Objects must be well formed
            &&& forall |kid: KernelObjectID| self.capabilities.contains_key(kid) ==> self.capabilities.index(kid).wf(self)
            &&& forall |kid: KernelObjectID| self.l1_cnodes.contains_key(kid) ==> self.l1_cnodes.index(kid).wf(self)
            &&& forall |kid: KernelObjectID| self.l2_cnodes.contains_key(kid) ==> self.l2_cnodes.index(kid).wf(self)
            &&& forall |kid: KernelObjectID| self.disps.contains_key(kid) ==> self.disps.index(kid).wf(self)
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Constants:
    ///////////////////////////////////////////////////////////////////////////
    
    pub spec const ENTRY_COUNT_L2CNODE: nat = 256;
    pub spec const ENTRY_COUNT_L1CNODE: nat = 256;
}
