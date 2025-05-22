/// MIT License
///
/// Copyright (c) 2025 Ilias Karimalis

use state_machines_macros::*;
use vstd::prelude::*;

use crate::barrelfish::cpudriver::*;
use crate::barrelfish::kpi::{CapRef, CNodeType, CapAddr, CapSlot};

verus!
{
    state_machine!
    {
        BarrelfishSingleCoreState {
            fields {
                pub state: CpuDriverState,
            }

            ///////////////////////////////////////////////////////////////////
            // Invariants:
            ///////////////////////////////////////////////////////////////////

            #[invariant]
            pub open spec fn capabilities_wf(&self) -> bool {
                forall |kid: KernelObjectID| self.state.capabilities.contains_key(kid) ==> self.state.capabilities.index(kid).wf(&self.state)
            }

            #[invariant]
            pub open spec fn l1_cnodes_wf(&self) -> bool {
                forall |kid: KernelObjectID| self.state.l1_cnodes.contains_key(kid) ==> self.state.l1_cnodes.index(kid).wf(&self.state)
            }

            #[invariant]
            pub open spec fn l2_cnodes_wf(&self) -> bool {
                forall |kid: KernelObjectID| self.state.l2_cnodes.contains_key(kid) ==> self.state.l2_cnodes.index(kid).wf(&self.state)
            }

            #[invariant]
            pub open spec fn disps_wf(&self) -> bool {
                forall |kid: KernelObjectID| self.state.disps.contains_key(kid) ==> self.state.disps.index(kid).wf(&self.state)
            }

            ///////////////////////////////////////////////////////////////////
            // Initialization:
            ///////////////////////////////////////////////////////////////////

            init!
            {
                initialize()
                {
                    init state = CpuDriverState {
                        capabilities: Map::empty(),
                        l1_cnodes: Map::empty(),
                        l2_cnodes: Map::empty(),
                        disps: Map::empty(),
                    };
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
                    require pre.state.disps.contains_key(pid);
                    let local: Dispatcher = pre.state.disps.index(pid);
                    let local_l1: L1CNodeObject = pre.state.l1_cnodes.index(local.cspace);

                    // 3. The src_root must point to a valid L1 CNode
                    let local_src_root_l2_cap: CapabilityObject = local_l1.index(src_root, &pre.state);
                    require local_src_root_l2_cap is L2CNode;
                    let local_src_root_l2: L2CNodeObject = pre.state.l2_cnodes.index(local_src_root_l2_cap->l2_kid);
                    let src_root_cap: CapabilityObject = local_src_root_l2.index(src_root, &pre.state);
                    require src_root_cap is L1CNode;
                    let src_cspace = pre.state.l1_cnodes.index(src_root_cap->l1_kid);

                    // 4. The src_addr must point to a non-null capability in the source cspace
                    require src_level != CNodeType::L1; 
                    let src_cspace_l2_cap: CapabilityObject = src_cspace.index(src_addr, &pre.state);
                    require src_cspace_l2_cap is L2CNode;
                    let src_cap: CapabilityObject = if (src_level is Cap) {
                        let src_cspace_l2 = pre.state.l2_cnodes.index(src_cspace_l2_cap->l2_kid);
                        src_cspace_l2.index(src_addr, &pre.state)
                    } else {
                        src_cspace.index(src_addr, &pre.state)
                    };
                    require !(src_cap is Null);
            
                    // 5. The dest_cspace must point to a valid L1 CNode
                    let local_dest_root_l2_cap = local_l1.index(dcs_addr, &pre.state);
                    require local_dest_root_l2_cap is L2CNode;
                    let local_dest_root_l2 = pre.state.l2_cnodes.index(local_dest_root_l2_cap->l2_kid);
                    let dest_root_cap = local_dest_root_l2.index(dcs_addr, &pre.state);
                    require dest_root_cap is L1CNode;
                    let dest_cspace = pre.state.l1_cnodes.index(dest_root_cap->l1_kid);

                    // 6. The dest_addr must point to a valid Null slot in the destination cspace
                    require dest_level != CNodeType::Cap;
                    let dest_cspace_l2_cap = dest_cspace.index(dcn_addr, &pre.state);
                    if (dest_level == CNodeType::L2) {
                        require dest_cspace_l2_cap is L2CNode;
                        let dest_cspace_l2 = pre.state.l2_cnodes.index(dest_cspace_l2_cap->l2_kid);
                        require dest_cspace_l2.index(dcn_addr, &pre.state) is Null;

                        // Update the destination cspace with the capability from the source cspace
                        update state = dest_cspace_l2.update(dcn_addr, src_cap, &pre.state);
                    } else {
                        require dest_cspace_l2_cap is Null;

                        // Update the destination cspace with the capability from the source cspace
                        update state = dest_cspace.update(dcn_addr, src_cap, &pre.state);
                    }
                }
            }


            ///////////////////////////////////////////////////////////////////
            /// Inductive proofs:
            ///////////////////////////////////////////////////////////////////

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(cap_copy)]
            fn cap_copy_inductive(pre: Self, post: Self, pid: KernelObjectID, dest: CapRef, source: CapRef) { }
        }
    }

}
