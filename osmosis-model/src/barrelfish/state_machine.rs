/// MIT License
///
/// Copyright (c) 2025 Ilias Karimalis

use state_machines_macros::*;
use vstd::prelude::*;

// use crate::capability::{self, KernelObject};
use crate::utils::Optional;
use crate::barrelfish::kpi::*;

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

    ///////////////////////////////////////////////////////////////////////////
    // L1 CNode Type
    ///////////////////////////////////////////////////////////////////////////

    /// The model representation of an L1 CNode.
    pub ghost struct L1CNodeObject {
        pub table: Seq<KernelObjectID>,
    }

    impl L1CNodeObject {

        // Checks that the CapAddr is a well formed access into this L1 Cnode
        pub open spec fn wf_access(&self, addr: CapAddr) -> bool {
            self.table.len() > addr.l1
        }

        /// Accesses the L1CNode and returns the KernelObjectID to the underlying capability
        pub open spec fn index_kid(&self, addr: CapAddr) -> KernelObjectID
            recommends self.wf_access(addr)
        {
            self.table.index(addr.l1)
        }

        /// Accesses the L1CNode and returns the Capability that resides in that slot
        pub open spec fn index(&self, addr: CapAddr, capabilities: Map<KernelObjectID, CapabilityObject>) -> CapabilityObject
            recommends self.wf_access(addr)
        {
            capabilities.index(self.table.index(addr.l1))
        }

        /// Updates the L1CNode with a new capability at the given address, returning the newly updated state
        pub open spec fn update(&self, addr: CapAddr, cap: CapabilityObject, capabilities: Map<KernelObjectID, CapabilityObject>) -> Map<KernelObjectID, CapabilityObject>
            recommends self.wf_access(addr) 
                && self.index(addr, capabilities) == CapabilityObject::Null
                && cap is L2CNode
        {
            let kid: KernelObjectID = self.table.index(addr.l1);
            capabilities.insert(kid, cap)
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
        // pub open spec fn wf(&self, capabilities: Map<KernelObjectID, CapabilityObject>) -> bool {
        //     // The length of an L2 CNode is the fixed size decided by the system architecture
        //     &&& self.table.len() == ENTRY_COUNT_L2CNODE
        //     // The entries of an L2CNode must all be valid capabilites
        //     &&& forall |kid: KernelObjectID| self.table.contains(kid) ==> {
        //         &&& capabilities.contains_key(kid)
        //         // The well formedness of the underlying capability is going to be checked by the
        //         // CpuDriverState wf check and does not need to be checked here.
        //         // &&& state.capabilities.index(kid).wf(state)
        //     }
        // }

        // Checks that CapSlot is a well formed access into this L2 Cnode
        pub open spec fn wf_access(&self, addr: CapAddr) -> bool {
            self.table.len() > addr.l2
        }

        /// Accesses the L2CNode and returns the KernelObjectID to the underlying capability
        pub open spec fn index_kid(&self, addr: CapAddr) -> KernelObjectID
            recommends self.wf_access(addr)
        {
            self.table.index(addr.l2)
        }

        /// Accesses the L2CNode and returns the Capability that resides in that slot
        pub open spec fn index(&self, addr: CapAddr, capabilities: Map<KernelObjectID, CapabilityObject>) -> CapabilityObject
            recommends self.wf_access(addr)
        {
            capabilities.index(self.table.index(addr.l2))
        }

        /// Updates the CPUDriverState with a new capability at the given address, returning the newly updated state
        pub open spec fn update(&self, addr: CapAddr, cap: CapabilityObject, capabilities: Map<KernelObjectID, CapabilityObject>) -> Map<KernelObjectID, CapabilityObject>
            recommends self.wf_access(addr)
                && self.index(addr, capabilities) == CapabilityObject::Null
        {
            let kid: KernelObjectID = self.table.index(addr.l2);
            capabilities.insert(kid, cap)
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
        pub open spec fn wf(&self, l1_cnodes: Map<KernelObjectID, L1CNodeObject>) -> bool {
            // The cspace of a dispatcher object must be in the kernel and well formed
            l1_cnodes.contains_key(self.cspace)
            // TODO we could make wf a proper recursive wf() condition and check it here.
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // CPU Driver State:
    ///////////////////////////////////////////////////////////////////////////

    /// A representation of a barrelfish cpu driver state.
    // pub ghost struct CpuDriverState {
    // }

    // impl CpuDriverState {
    //     pub open spec fn wf(&self) -> bool {
    //         /// All Kernel Objects must be well formed
    //         &&& forall |kid: KernelObjectID| self.capabilities.contains_key(kid) ==> self.capabilities.index(kid).wf(self)
    //         &&& forall |kid: KernelObjectID| self.l1_cnodes.contains_key(kid) ==> self.l1_cnodes.index(kid).wf(self)
    //         &&& forall |kid: KernelObjectID| self.l2_cnodes.contains_key(kid) ==> self.l2_cnodes.index(kid).wf(self)
    //         &&& forall |kid: KernelObjectID| self.disps.contains_key(kid) ==> self.disps.index(kid).wf(self)
    //     }
    // }

    ///////////////////////////////////////////////////////////////////////////
    // Constants:
    ///////////////////////////////////////////////////////////////////////////
    
    pub spec const ENTRY_COUNT_L2CNODE: nat = 256;
    pub spec const ENTRY_COUNT_L1CNODE: nat = 256;


    /////////////////////////////////////////////////////////////////////////
    // State Machine:
    /////////////////////////////////////////////////////////////////////////
    
    
    state_machine!
    {
    BarrelfishSingleCoreKernelState {
        fields {
            /// The set of valid capabilities
            pub capabilities: Map<KernelObjectID, CapabilityObject>,
            /// The set of valid L1 CNodes
            pub l1_cnodes: Map<KernelObjectID, L1CNodeObject>,
            /// The set of valid L2 CNodes
            pub l2_cnodes: Map<KernelObjectID, L2CNodeObject>,
            /// The set of dispatchers 
            pub disps: Map<KernelObjectID, Dispatcher>
        }

        ///////////////////////////////////////////////////////////////////
        // Invariants:
        ///////////////////////////////////////////////////////////////////

        #[invariant]
        pub open spec fn capabilities_wf(&self) -> bool {
            forall |kid: KernelObjectID| self.capabilities.contains_key(kid) ==> match(self.capabilities.index(kid)) { 
                CapabilityObject::Null => true,
                CapabilityObject::L1CNode { l1_kid } => self.l1_cnodes.contains_key(l1_kid),
                CapabilityObject::L2CNode { l2_kid } => self.l2_cnodes.contains_key(l2_kid),
            }
        }

        #[invariant]
        pub open spec fn l1_cnodes_wf(&self) -> bool {
            forall |kid: KernelObjectID| self.l1_cnodes.contains_key(kid) ==> {
                let l1: L1CNodeObject = self.l1_cnodes.index(kid);
                // The length of an L1 CNode must be a multiple of L2 CNode size
                &&& l1.table.len() >= ENTRY_COUNT_L1CNODE || l1.table.len() % ENTRY_COUNT_L1CNODE == 0
                // The entries of an L1CNode must all be valid capabilities that are either Null or L2CNode capabilities.
                &&& forall |kid: KernelObjectID| l1.table.contains(kid) ==> {
                    &&& self.capabilities.contains_key(kid)
                    &&& self.capabilities.index(kid) is Null || self.capabilities.index(kid) is L2CNode
                }
            }
        }

        #[invariant]
        pub open spec fn l2_cnodes_wf(&self) -> bool {
            forall |kid: KernelObjectID| self.l2_cnodes.contains_key(kid) ==> {
                let l2: L2CNodeObject = self.l2_cnodes.index(kid);
                // The length of an L2 CNode must be a multiple of the size of the capability
                &&& l2.table.len() == ENTRY_COUNT_L2CNODE
                // The entries of an L2CNode must all be valid capabilities that are either Null or L1CNode capabilities.
                &&& forall |kid: KernelObjectID| l2.table.contains(kid) ==> {
                    &&& self.capabilities.contains_key(kid)
                    &&& self.capabilities.index(kid) is Null || self.capabilities.index(kid) is L1CNode
                }
            }
        }

        #[invariant]
        pub open spec fn disps_wf(&self) -> bool {
            forall |kid: KernelObjectID| self.disps.contains_key(kid) ==> {
                let disp: Dispatcher = self.disps.index(kid);
                // The cspace of a dispatcher object must be a valid L1 CNode
                self.l1_cnodes.contains_key(disp.cspace)
            }
        }

        ///////////////////////////////////////////////////////////////////
        // Initialization:
        ///////////////////////////////////////////////////////////////////

        init!
        {
            initialize()
            {
                init capabilities = Map::empty();
                init l1_cnodes = Map::empty();
                init l2_cnodes = Map::empty();
                init disps = Map::empty();
            }
        }

        transition! {
            cap_copy(
                // KernelObjectID of the calling dispatcher
                pid: KernelObjectID,
                // Location of the destination slot, which must be empty
                dest: CapRef,
                // Location of the source capability
                source: CapRef)
            {
                // For this to be a valid transition, we must have:
                // 1. source and dest must both be non-null capability references
                require !dest.is_null();
                require !source.is_null();

                // Address of the destination root cnode relative to the caller's cspace
                let dcs_addr: CapAddr = dest.get_croot_addr();
                // Address at which to place the capability relative to the destination cspace
                let dcn_addr: CapAddr = dest.get_cnode_addr();
                // Level of the destination CNode
                let dest_level: CNodeType = dest.get_cnode_level();
                // Addres of the source root cnode relative to the caller's cspace 
                let src_root: CapAddr = source.get_croot_addr();
                // Address of the source capability relative to the source cspace
                let src_addr: CapAddr = source.get_cnode_addr();
                // Level of the source capability
                let src_level: CNodeType = source.get_cap_level();

                // 2. pid must point to a Dispatcher
                require pre.disps.contains_key(pid);
                let local: Dispatcher = pre.disps.index(pid);
                let local_l1: L1CNodeObject = pre.l1_cnodes.index(local.cspace);

                // 3. The src_root must point to a valid L1 CNode
                let local_src_root_l2_cap: CapabilityObject = local_l1.index(src_root, pre.capabilities);
                require local_src_root_l2_cap is L2CNode;
                let local_src_root_l2: L2CNodeObject = pre.l2_cnodes.index(local_src_root_l2_cap->l2_kid);
                let src_root_cap: CapabilityObject = local_src_root_l2.index(src_root, pre.capabilities);
                require src_root_cap is L1CNode;
                let src_cspace = pre.l1_cnodes.index(src_root_cap->l1_kid);

                // 4. The src_addr must point to a non-null capability in the source cspace
                require src_level != CNodeType::L1; 
                let src_cspace_l2_cap: CapabilityObject = src_cspace.index(src_addr, pre.capabilities);
                require src_cspace_l2_cap is L2CNode;
                let src_cap: CapabilityObject = if (src_level is Cap) {
                    let src_cspace_l2 = pre.l2_cnodes.index(src_cspace_l2_cap->l2_kid);
                    src_cspace_l2.index(src_addr, pre.capabilities)
                } else {
                    src_cspace.index(src_addr, pre.capabilities)
                };
                require !(src_cap is Null);
        
                // 5. The dest_cspace must point to a valid L1 CNode
                let local_dest_root_l2_cap = local_l1.index(dcs_addr, pre.capabilities);
                require local_dest_root_l2_cap is L2CNode;
                let local_dest_root_l2 = pre.l2_cnodes.index(local_dest_root_l2_cap->l2_kid);
                let dest_root_cap = local_dest_root_l2.index(dcs_addr, pre.capabilities);
                require dest_root_cap is L1CNode;
                let dest_cspace = pre.l1_cnodes.index(dest_root_cap->l1_kid);

                // 6. The dest_addr must point to a valid Null slot in the destination cspace
                require dest_level != CNodeType::Cap;
                let dest_cspace_l2_cap = dest_cspace.index(dcn_addr, pre.capabilities);
                if (dest_level == CNodeType::L2) {
                    require dest_cspace_l2_cap is L2CNode;
                    let dest_cspace_l2 = pre.l2_cnodes.index(dest_cspace_l2_cap->l2_kid);
                    require dest_cspace_l2.index(dcn_addr, pre.capabilities) is Null;

                    // Update the destination cspace with the capability from the source cspace
                    update capabilities = dest_cspace_l2.update(dcn_addr, src_cap, pre.capabilities);
                } else {
                    require dest_cspace_l2_cap is Null;

                    // Update the destination cspace with the capability from the source cspace
                    update capabilities = dest_cspace.update(dcn_addr, src_cap, pre.capabilities);
                }
            }
        }


        ///////////////////////////////////////////////////////////////////
        /// Inductive proofs:
        ///////////////////////////////////////////////////////////////////

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(cap_copy)]
        fn cap_copy_inductive(pre: Self, post: Self, pid: KernelObjectID, dest: CapRef, source: CapRef) { 
            // TODO!
         }
    }
}
}
