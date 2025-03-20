/// MIT License
///
/// Copyright (c) 2025 Ilias Karimalis

use vstd::prelude::*;

verus!
{

/// Protection Domain
pub ghost struct ProtectionDomain {
    pub id: nat,
}

impl ProtectionDomain {
    pub closed spec fn new(id: nat) -> ProtectionDomain {
        ProtectionDomain { id }
    }

    /// Obtains the id of a Protections domain
    pub open spec fn id(&self) -> nat {
        self.id
    }
}

/// Resource
pub ghost struct Resource {
    pub rtype: ResourceType,
    pub val: nat,
}

impl Resource {
    /// Obtains the type of the Resource
    pub open spec fn rtype(&self) -> ResourceType {
        self.rtype
    }

    /// Obtains the identifying value of the Resource
    pub open spec fn val(&self) -> nat {
        self.val
    }
}

/// Resource Space
pub ghost struct ResourceSpace {
    pub rtype: ResourceType,
    pub vals: Set<nat>,
}

impl ResourceSpace {
    /// Obtains the type of the ResourceSpace
    pub open spec fn rtype(&self) -> ResourceType {
        self.rtype
    }

    /// Obtains the identifying values of the ResourceSpace
    pub open spec fn vals(&self) -> Set<nat> {
        self.vals
    }
}

/// Resource Type
pub ghost enum ResourceType {
    Virtual(nat),
    Physical(nat),
}

pub ghost enum ResourceLike {
    Resource { res: Resource },
    Space { space: ResourceSpace },
}

impl ResourceLike {
    /// Obtains the type of the ResourceLike
    pub open spec fn rtype(&self) -> ResourceType {
        match self {
            ResourceLike::Resource { res } => res.rtype(),
            ResourceLike::Space { space } => space.rtype(),
        }
    }
}

/// Hold edge
pub ghost struct HoldEdge {
    pub src: ProtectionDomain,
    pub dst: ResourceLike,
}

impl HoldEdge {
    pub open spec fn src(&self) -> ProtectionDomain {
        self.src
    }

    pub open spec fn dst(&self) -> ResourceLike {
        self.dst
    }
}

/// Map edge
pub ghost enum MapEdge {
    SpaceBacking { sb_src: ResourceSpace, sb_dst: Resource },
    SpaceMap { sm_src: ResourceSpace, sm_dst: ResourceSpace },
    ResourceMap { rm_src: Resource, rm_dst: Resource },
}

impl MapEdge {
    pub open spec fn well_formed(self) -> bool {
        //  Physical src can't map to a Virtual dst
        match (self) {
            MapEdge::SpaceBacking { sb_src, sb_dst } => sb_src.rtype() is Physical ==> sb_dst.rtype() is Physical,
            MapEdge::SpaceMap { sm_src, sm_dst } => sm_src.rtype() is Physical ==> sm_dst.rtype() is Physical,
            MapEdge::ResourceMap { rm_src, rm_dst } => rm_src.rtype() is Physical ==> rm_dst.rtype() is Physical,
        }
    }
}

/// Subset edge
pub ghost struct SubsetEdge {
    pub src: Resource,
    pub dst: ResourceSpace,
}

impl SubsetEdge {
    pub open spec fn src(&self) -> Resource {
        self.src
    }

    pub open spec fn dst(&self) -> ResourceSpace {
        self.dst
    }

    pub open spec fn well_formed(self) -> bool {
        // The val of the src Resource must be managed by the space that it subsets
        &&& self.dst().vals().contains(
            self.src().val()
        )
        // The src and dst must share a type
        &&& self.src().rtype() == self.dst().rtype()
    }
}

/// Request edge
pub ghost struct RequestEdge {
    pub src: ProtectionDomain,
    pub dst: ProtectionDomain,
    pub rtype: ResourceType,
}

impl RequestEdge {
    pub open spec fn src(&self) -> ProtectionDomain {
        self.src
    }

    pub open spec fn dst(&self) -> ProtectionDomain {
        self.dst
    }

    pub open spec fn rtype(&self) -> ResourceType {
        self.rtype
    }
}

}
