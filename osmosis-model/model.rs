use state_machines_macros::*;
use vstd::prelude::*;

use vstd::set::Set;

verus! {

/// A Protection Domain
pub ghost struct ProtectionDomain { pub id: nat }

impl ProtectionDomain {
    pub closed spec fn new(id: nat) -> ProtectionDomain {
        ProtectionDomain { id }
    }

    /// Obtains the id of a Protections domain
    pub open spec fn id(&self) -> nat {
        self.id
    }
}

/// A Resource
pub ghost struct Resource { 
    pub rtype: ResourceType, 
    pub val: nat 
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

/// A Resource Space
pub ghost struct ResourceSpace { 
    pub rtype: ResourceType, 
    pub vals: Set<nat> 
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

/// A Resource Type
pub ghost enum ResourceType { Virtual(nat), Physical(nat) }

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

/// A Hold edge
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

pub ghost struct MapEdge {
    pub src: ResourceLike,
    pub dst: ResourceLike,
}

impl MapEdge {
    pub open spec fn src(&self) -> ResourceLike {
        self.src
    }

    pub open spec fn dst(&self) -> ResourceLike {
        self.dst
    }

    // #[verifier::type_invariant]
    pub open spec fn well_formed(self) -> bool { 
        // A Physical Resource(Space), can't map to a Virtual Resource(Space)
        &&& self.src().rtype() is Physical ==> self.dst().rtype() is Physical
        // If the src node is a resource then the dst must be a resource
        &&& self.src() is Resource ==> self.dst() is Resource
    }
}

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
        &&& self.dst().vals().contains(self.src().val())
        // The src and dst must share a type
        &&& self.src().rtype() == self.dst().rtype()
    }
}

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

state_machine! {
    osmosis_dag {
        fields {
            /// The protection domains of the Osmosis DAG
            pub domains: Set<ProtectionDomain>,
            /// The resources of the Osmosis DAG
            pub resources: Set<Resource>,
            /// The resource spaces of the Osmosis DAG
            pub spaces: Set<ResourceSpace>,
            /// The Hold edges of the Osmosis DAG
            pub holds: Set<HoldEdge>,
            /// The Map edges of the Osmosis DAG
            pub maps: Set<MapEdge>,
            /// The Subset edges of the Osmosis DAG
            pub subsets: Set<SubsetEdge>,
            /// The Request edges of the Osmosis DAG
            pub requests: Set<RequestEdge>,
        }

        // Invariants:

        /// The model must have a finite number of protection domains
        #[invariant]
        pub open spec fn domains_is_finite(&self) -> bool {
            self.domains.finite()
        }

        /// The model must have a finite number of resources
        #[invariant]
        pub open spec fn resources_is_finite(&self) -> bool {
            self.resources.finite()
        }

        /// The model must have a finite number of resource spaces
        #[invariant]
        pub open spec fn spaces_is_finite(&self) -> bool {
            self.spaces.finite()
        }

        /// The model must have a finite number of hold edges
        #[invariant]
        pub open spec fn holds_is_finite(&self) -> bool {
            self.holds.finite()
        }

        /// The hold edges must point to nodes in the graph
        #[invariant]
        pub open spec fn hold_nodes_in_graph(&self) -> bool {
            forall |e: HoldEdge|  #[trigger] self.holds.contains(e) ==> {
                &&& self.domains.contains(e.src()) 
                &&& e.dst() is Resource ==> self.resources.contains(e.dst()->res)
                &&& e.dst() is Space ==> self.spaces.contains(e.dst()->space)
            }
        }

        /// There must be at least one hold edge to each resource in the graph
        #[invariant]
        pub open spec fn hold_edge_to_each_resource(&self) -> bool {
            forall |r: Resource|   self.resources.contains(r) ==> 
                exists |e: HoldEdge|  self.holds.contains(e) && e.dst() is Resource && e.dst()->res == r
        }

        /// There must be at least one hold edge to each resource space in the graph
        #[invariant]
        pub open spec fn hold_edge_to_each_space(&self) -> bool {
            forall |s: ResourceSpace|  self.spaces.contains(s) ==>
                exists |e: HoldEdge| self.holds.contains(e) && e.dst() is Space && e.dst()->space == s
        }

        /// The model must have a finite number of map edges
        #[invariant]
        pub open spec fn maps_is_finite(&self) -> bool {
            self.maps.finite()
        }

        /// Map edges must be well formed
        #[invariant]
        pub open spec fn map_edges_well_formed(&self) -> bool {
            forall |me: MapEdge| self.maps.contains(me) ==> me.well_formed()
        }

        /// The map edges must be between nodes in the grpah
        #[invariant]
        pub open spec fn map_nodes_in_graph(&self) -> bool {
            forall |e: MapEdge|  self.maps.contains(e) ==> {
                &&& e.src() is Resource ==> self.resources.contains(e.src()->res)
                &&& e.src() is Space ==> self.spaces.contains(e.src()->space)
                &&& e.dst() is Resource ==> self.resources.contains(e.dst()->res)
                &&& e.dst() is Space ==> self.spaces.contains(e.dst()->space)
            }
        }

        /// Every resource space in the model needs to map to either a resource or another space
        #[invariant]
        pub open spec fn spaces_are_mapped(&self) -> bool {
            forall |s: ResourceSpace|  self.spaces.contains(s) ==>
                exists |e: MapEdge| self.maps.contains(e) && e.src() is Space && e.src()->space == s
        }

        /// Notes (2025-02-12)
        ///
        /// I wonder what more we can say about Map edges, for example is it reasonable to
        /// constrain Map edges such that they only ever Map Physical to Physical. Shaurya brought
        /// up a sort of counterexample for this, of cxl where writing to a physical address that
        /// corresponds to pcie memory results in a virtual address lookup in the cxl bus, which
        /// will eventually map to a physical address across the cxl band. I think that this can be
        /// worked around by treating physical pcie memory as a virtual resource.
        ///
        /// This does bring up the question of whether or not we should allow multiple outgoing map
        /// edges from a resource space to other resource spaces. My inclination is to say yes, but
        /// I haven't come up with an example for this being useful other than pcie/device
        /// memory being embedded into normal physical memory accesses.
        ///
        /// For now I'm going to perform this physical to physical constraint, but I'm not sure
        /// that it's necessary nor useful.
        #[invariant]
        pub open spec fn physical_spaces_map_to_physical_spaces(&self) -> bool {
            forall |e: MapEdge| self.maps.contains(e) && e.src().rtype() is Physical ==> e.dst().rtype() is Physical 
        }

        /// map edges whose source is a resource, must have a resource as a destination.
        #[invariant]
        pub open spec fn resources_map_to_resources(&self) -> bool {
            forall |e: MapEdge| self.maps.contains(e) && e.src() is Resource ==> e.dst() is Resource
        }

        /// The model must have a finite number of subset edges
        #[invariant]
        pub open spec fn subsets_is_finite(&self) ->  bool {
            self.subsets.finite()
        }

        /// Subset edges must be well formed
        #[invariant]
        pub open spec fn subset_edges_well_formed(&self) -> bool {
            forall |se: SubsetEdge| self.subsets.contains(se) ==> se.well_formed()
        }

        /// Subset edges must be between nodes in the graph
        #[invariant]
        pub open spec fn subset_nodes_in_graph(&self) -> bool {
            forall |e: SubsetEdge|  self.subsets.contains(e) ==> {
                &&& self.resources.contains(e.src())
                &&& self.spaces.contains(e.dst())
            }
        }

        /// All resource nodes in the graph must be the source in a subset edge
        #[invariant]
        pub open spec fn resources_are_subset(&self) -> bool {
            forall |r: Resource| self.resources.contains(r) ==> 
                exists |e: SubsetEdge| self.subsets.contains(e) && e.src() == r
        }

        pub open spec fn subset_src_are_unique(&self) -> bool {
            forall |e1, e2: SubsetEdge| self.subsets.contains(e1) && self.subsets.contains(e2) && e1.src() == e2.src() ==> e1.dst() == e2.dst()
        }

        /// The model must have a finite number of request edges
        #[invariant]
        pub open spec fn requests_is_finite(&self) -> bool {
            self.requests.finite()
        }


        // Initalize:

        init! {
            initialize() 
            {
                init domains = Set::empty();
                init resources = Set::empty();
                init spaces = Set::empty();
                init holds = Set::empty();
                init maps = Set::empty();
                init subsets = Set::empty();
                init requests = Set::empty();
            }
        }

        // Transitions:

        /// Create a new resource node. This is done by subsetting it from a specific resource space
        transition! {
            create_resource(res: Resource, space: ResourceSpace, holder: ProtectionDomain) 
            {
                // The Protection Domain must exist
                require pre.domains.contains(holder);
                // The Resource Space must exist
                require pre.spaces.contains(space);
                // The new Resource must not already exist
                require !pre.resources.contains(res);
                // There must be a hold edge from the holder protection domain to the resource space
                require exists |he: HoldEdge| 
                    pre.holds.contains(he) 
                    && he.src() == holder 
                    && he.dst() is Space 
                    && he.dst()->space == space;
                // The Resource must be of the same type as the Resource Space
                require res.rtype() == space.rtype();
                // The value must be in the Resource Space
                require space.vals().contains(res.val());
                // The Resource must not already be held
                require !pre.holds.contains(HoldEdge { src: holder, dst: ResourceLike::Resource { res } });
                // There must be a hold edge from the holder to the space
                require pre.holds.contains(HoldEdge { src: holder, dst: ResourceLike::Space { space } });

                update resources = pre.resources.insert(res);
                update subsets = pre.subsets.insert(SubsetEdge { src: res, dst: space });
                update holds = pre.holds.insert(HoldEdge { src: holder, dst: ResourceLike::Resource { res }});
            }
        }

        /// Notes (2025-03-14)
        ///
        /// I'm not sure how we should limit/which requirements we should set on Resources which
        /// can be destroyed. For now, the only requirement I'm setting is that this Resource must
        /// not be in use as the backing Resource for a ResourceSpace. The alternative I can think
        /// of here is recursively deleting the ResourceSpace, maybe this is someting to discuss
        /// with @Reto.
        transition! {
            destroy_resource(res: Resource)
            {
                // The Resource must exist
                require pre.resources.contains(res);
                // The Resource must not be the backing resource of a ResourceSpace
                require forall |me: MapEdge| pre.maps.contains(me) && me.dst() is Resource && me.dst()->res == res ==> me.src() is Resource;

                let se = choose |se: SubsetEdge| pre.subsets.contains(se) && se.src() == res;
                let reslike = ResourceLike::Resource { res };
                let hold_edge_filter = |he: HoldEdge| -> (bool) { he.dst() != reslike };
                let map_edge_filter = |me: MapEdge| -> (bool) { me.src() != reslike && me.dst() != reslike };
                
                update resources = pre.resources.remove(res);
                update subsets = pre.subsets.remove(se);
                update holds = pre.holds.filter(hold_edge_filter);
                update maps = pre.maps.filter(map_edge_filter);
            }
        }

        // Inductiveness Proofs:
        
        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(create_resource)]
        fn create_resource_inductive(pre: Self, post: Self, res: Resource, space: ResourceSpace, holder: ProtectionDomain) 
        {
            // Invariant hold_edge_to_each_resource
            assert forall |r: Resource| post.resources.contains(r) implies
                exists |e: HoldEdge| post.holds.contains(e) && e.dst() is Resource && e.dst()->res == r by {
                    let e = if (r == res) {
                        HoldEdge { src: holder, dst: ResourceLike::Resource { res }}
                    } else {
                        choose |e| pre.holds.contains(e) && e.dst() is Resource && e.dst()->res == r 
                    };
                    assert(post.holds.contains(e) && e.dst() is Resource && e.dst()->res == r);
                }
            
            // Invariant: hold_edge_to_each_space
            assert forall |s: ResourceSpace| post.spaces.contains(s) implies
                exists |e: HoldEdge| post.holds.contains(e) && e.dst() is Space && e.dst()->space == s by {
                    let e = choose |e| pre.holds.contains(e) && e.dst() is Space && e.dst()->space == s;
                    assert(post.holds.contains(e) && e.dst() is Space && e.dst()->space == s);
                }
            
            // Invariant: resources_are_subsets
            assert forall |r: Resource| post.resources.contains(r) implies 
                exists |e: SubsetEdge| post.subsets.contains(e) && e.src() == r by {
                    let e = if (r == res) {
                        SubsetEdge { src: res, dst: space }
                    } else {
                        choose |e| pre.subsets.contains(e) && e.src() == r
                    };
                    assert(post.subsets.contains(e) && e.src() == r);
                }
        }

        #[inductive(destroy_resource)]
        fn destroy_resource_inductive(pre: Self, post: Self, res: Resource)
        {

        }

        // Helper functions:

        }
    }
}

