/// MIT License
///
/// Copyright (c) 2025 Ilias Karimalis

use state_machines_macros::*;
use vstd::prelude::*;

use crate::barrelfish::cpudriver::*;

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

            //transition!
            //{
            //    cap_copy(pid: KernelObjectID)
            //    {
            //        
            //    }
            //}
            //

            transition! 
            {
                // 
                // \param pid              KernelObjectID of the calling dispatcher
                // \param dest_cspace_cptr Destnation cspace root cnode cptr in source cspace
                // \param destcn_cptr      Destination cnode cptr relative to destination cspace
                // \param dest_slot        Destination slot
                // \param source_cptr      Souurce capability cptr retative to source cspace
                // \param destcn_level     Level/depth of destination cnode
                // \param source_level     Level/depth of source cap
                cap_copy(pid: KernelObjectID, 
                         dest_cspace_cptr: CapAddr,
                         destcn_cptr: CapAddr,
                         dest_slot: CapSlot,
                         source_cptr: CapAddr,
                         destcn_level: bool,
                         source_level: bool)
            }


            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }


        }
    }

}
