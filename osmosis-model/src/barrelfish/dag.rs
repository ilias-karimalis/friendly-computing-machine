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
        }
    }

}
