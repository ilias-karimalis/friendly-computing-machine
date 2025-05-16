/// MIT License
///
/// Copyright (c) 2025 Ilias Karimalis

use state_machines_macros::*;
use vstd::prelude::*;

verus! {

    pub spec const U24_MAX: int = 0x0FFFFFF;
    pub spec const U8_MAX:  int = 0x0FF;

    pub ghost struct CapAddr {
        /// Index into the L1 CNode
        pub l1: int,
        /// Index into the L2 CNode
        pub l2: int,
    }

    impl CapAddr {
        pub open spec fn wf(&self) -> bool {
            // The L1 index must fit into a 24 bit value
            &&& 0 <= self.l1 <= U24_MAX
            // The L2 index must fit into an 8 bit value
            &&& 0 <= self.l2 <= U8_MAX
        }
    }

    pub ghost struct CapSlot {
        pub idx: int,
    }

    impl CapSlot {
        pub open spec fn wf(&self) -> bool {
            0 <= self.idx <= U8_MAX
        }
    }
}
