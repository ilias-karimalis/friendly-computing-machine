/// MIT License
///
/// Copyright (c) 2025 Ilias Karimalis

use crate::dag::*;

verus!
{

pub ghost enum Capability {
    Null,
    PhysAddr { base: nat, bytes: nat },
    DevFrame { base: nat, bytes: nat },
    RAM { base: nat, bytes: nat  },
    Frame { base: nat, bytes: nat },
    Dispatcher,
    L1_CNode,
    L2_CNode,
    IDC_Endpoint,
    VNode_AARCH64_L0,
    VNode_AARCH64_L1,
    VNode_AARCH64_L2,
    VNode_AARCH64_L3,
    VNode_AARCH64_L0_Mapping,
    VNode_AARCH64_L1_Mapping,
    VNode_AARCH64_L2_Mapping,
    VNode_AARCH64_L3_Mapping,
}



} // verus!

