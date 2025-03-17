use state_machines_macros::*;
use vstd::prelude::*;

use vstd::set::Set;

verus! {

/// A Protection Domain
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

/// A Resource
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

/// A Resource Space
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

/// A Resource Type
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

pub ghost enum MapEdgeR {
    SpaceBacking { sb_src: ResourceSpace, sb_dst: Resource },
    SpaceMap { sm_src: ResourceSpace, sm_dst: ResourceSpace },
    ResourceMap { rm_src: Resource, rm_dst: Resource },
}

impl MapEdgeR {
    //pub open spec fn src(&self) -> ResourceLike {
    //    self.src
    //}

    //pub open spec fn dst(&self) -> ResourceLike {
    //    self.dst
    //}

    pub open spec fn well_formed(self) -> bool {
        //  Physical src can't map to a Virtual dst
        match (self) {
            MapEdgeR::SpaceBacking { sb_src, sb_dst } => sb_src.rtype() is Physical ==> sb_dst.rtype() is Physical,
            MapEdgeR::SpaceMap { sm_src, sm_dst } => sm_src.rtype() is Physical ==> sm_dst.rtype() is Physical,
            MapEdgeR::ResourceMap { rm_src, rm_dst } => rm_src.rtype() is Physical ==> rm_dst.rtype() is Physical,
        }
    }
}

//pub ghost struct MapEdge {
//    pub src: ResourceLike,
//    pub dst: ResourceLike,
//}
//
//impl MapEdge {
//    pub open spec fn src(&self) -> ResourceLike {
//        self.src
//    }
//
//    pub open spec fn dst(&self) -> ResourceLike {
//        self.dst
//    }
//
//    // #[verifier::type_invariant]
//    pub open spec fn well_formed(self) -> bool {
//        // A Physical Resource(Space), can't map to a Virtual Resource(Space)
//        &&& self.src().rtype() is Physical
//            ==> self.dst().rtype() is Physical
//        // If the src node is a resource then the dst must be a resource
//        &&& self.src() is Resource ==> self.dst() is Resource
//    }
//}

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
            pub maps: Set<MapEdgeR>,
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
            forall |e: HoldEdge| #[trigger] self.holds.contains(e) ==> {
                &&& self.domains.contains(e.src())
                &&& e.dst() is Resource ==> self.resources.contains(e.dst()->res)
                &&& e.dst() is Space ==> self.spaces.contains(e.dst()->space)
            }
        }

        /// There must be at least one hold edge to each resource in the graph
        #[invariant]
        pub open spec fn hold_edge_to_each_resource(&self) -> bool {
            forall |r: Resource|   self.resources.contains(r) ==>
                exists |e: HoldEdge| #[trigger]  self.holds.contains(e) && e.dst() is Resource && e.dst()->res == r
        }

        /// There must be at least one hold edge to each resource space in the graph
        #[invariant]
        pub open spec fn hold_edge_to_each_space(&self) -> bool {
            forall |s: ResourceSpace|  self.spaces.contains(s) ==>
                exists |e: HoldEdge| #[trigger] self.holds.contains(e) && e.dst() is Space && e.dst()->space == s
        }

        /// The model must have a finite number of map edges
        #[invariant]
        pub open spec fn maps_is_finite(&self) -> bool {
            self.maps.finite()
        }

        /// Map edges must be well formed
        #[invariant]
        pub open spec fn map_edges_well_formed(&self) -> bool {
            forall |me: MapEdgeR| self.maps.contains(me) ==> #[trigger] me.well_formed()
        }

        /// The map edges must be between nodes in the grpah
        #[invariant]
        pub open spec fn map_nodes_in_graph(&self) -> bool {
            forall |e: MapEdgeR|  #[trigger] self.maps.contains(e) ==> {
                &&& e is SpaceBacking ==> self.spaces.contains(e->sb_src) && self.resources.contains(e->sb_dst)
                &&& e is SpaceMap ==> self.spaces.contains(e->sm_src) && self.spaces.contains(e->sm_dst)
                &&& e is ResourceMap ==> self.resources.contains(e->rm_src) && self.resources.contains(e->rm_dst)
            }
        }

        /// Every resource space in the model needs to map to either a resource or another space
        #[invariant]
        pub open spec fn spaces_are_mapped(&self) -> bool {
            forall |s: ResourceSpace|  self.spaces.contains(s) ==>
                exists |e: MapEdgeR| #[trigger] self.maps.contains(e) && ({
                    ||| e is SpaceBacking && e->sb_src == s
                    ||| e is SpaceMap && e->sm_src == s
                })
        }

        /// Note (2025-02-12)
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
        ///
        /// Note (2025-03-16)
        ///
        /// I think this is entriely captured by the map_edges_well_formed invariant and can be
        /// removed for now, it might need exapnding if we ever attach more information to
        /// ResourceTypes.
        //#[invariant]
        //pub open spec fn physical_spaces_map_to_physical_spaces(&self) -> bool {
        //    forall |e: MapEdge| self.maps.contains(e) && e.src().rtype() is Physical ==> e.dst().rtype() is Physical
        //}


        /// Note (2025-03-16)
        ///
        /// The redefinition of MapEdge as an Enum with thre variants structurally captures this
        /// invariant so it's no longer needed.
        ///
        /// map edges whose source is a resource, must have a resource as a destination.
        //#[invariant]
        //pub open spec fn resources_map_to_resources(&self) -> bool {
        //    forall |e: MapEdge| self.maps.contains(e) && e.src() is Resource ==> e.dst() is Resource
        //}

        /// The model must have a finite number of subset edges
        #[invariant]
        pub open spec fn subsets_is_finite(&self) ->  bool {
            self.subsets.finite()
        }

        /// Subset edges must be well formed
        #[invariant]
        pub open spec fn subset_edges_well_formed(&self) -> bool {
            forall |se: SubsetEdge| self.subsets.contains(se) ==> #[trigger] se.well_formed()
        }

        /// Subset edges must be between nodes in the graph
        #[invariant]
        pub open spec fn subset_nodes_in_graph(&self) -> bool {
            forall |e: SubsetEdge| #[trigger] self.subsets.contains(e) ==> {
                &&& self.resources.contains(e.src())
                &&& self.spaces.contains(e.dst())
            }
        }

        /// All resource nodes in the graph must be the source in a subset edge
        #[invariant]
        pub open spec fn resources_are_subset(&self) -> bool {
            forall |r: Resource| self.resources.contains(r) ==>
                exists |e: SubsetEdge| self.subsets.contains(e) && #[trigger] e.src() == r
        }

        #[invariant]
        pub open spec fn subset_src_are_unique(&self) -> bool {
            forall |e1: SubsetEdge, e2: SubsetEdge| 
                #[trigger] self.subsets.contains(e1) && #[trigger] self.subsets.contains(e2) && e1.src() == e2.src() ==> e1.dst() == e2.dst()
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
                    && #[trigger] he.src() == holder
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

        /// Note (2025-03-14)
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
                // The Resource must not be mapped or being used to map
                require forall |me: MapEdgeR| #[trigger] pre.maps.contains(me) ==> ({
                    ||| me is SpaceBacking && me->sb_dst != res
                    ||| me is SpaceMap 
                    ||| me is ResourceMap && me->rm_src != res && me->rm_dst != res });

                let se = choose |se: SubsetEdge| #[trigger] pre.subsets.contains(se) && se.src() == res;
                let reslike = ResourceLike::Resource { res };
                let hold_edge_filter = |he: HoldEdge| -> (bool) { he.dst() != reslike };

                update resources = pre.resources.remove(res);
                update subsets = pre.subsets.remove(se);
                update holds = pre.holds.filter(hold_edge_filter);
            }
        }

        /// Creates an empty ProtectionDomain
        transition! {
            create_pd(pd: ProtectionDomain)
            {
                // The ProtectionDomain must not already exist
                require !pre.domains.contains(pd);
                
                update domains = pre.domains.insert(pd);
            }
        }

        /// Destroy an empty ProtectionDomain
        transition! {
            destroy_pd(pd: ProtectionDomain)
            {
                // The ProtectionDomain must already exist
                require pre.domains.contains(pd);
                // There should be no edges from/towards this protection domain
                require forall |he: HoldEdge| pre.holds.contains(he) ==> #[trigger] he.src() != pd;
                require forall |re: RequestEdge| #[trigger] pre.requests.contains(re) ==> re.src() != pd && re.dst() != pd;

                update domains = pre.domains.remove(pd);
            }
        }

        /// Insert a RequestEdge 
        transition! {
            create_request_edge(req: RequestEdge)
            {
                // The two ProtectionDomains must already exist
                require pre.domains.contains(req.src());
                require pre.domains.contains(req.dst()); 
                // The dst ProtectionDomain must be holding a ResourceSpace of the requested type
                require exists |he: HoldEdge| pre.holds.contains(he) && #[trigger] he.src() == req.dst() && he.dst() is Space && he.dst()->space.rtype() == req.rtype();

                update requests = pre.requests.insert(req);
            }
        }

        /// Remove a RequestEdge
        transition! {
            destroy_request_edge(req: RequestEdge)
            {
                // The request edge must be in the graph
                require pre.requests.contains(req);

                update requests = pre.requests.remove(req);
            }
        }

        /// Note (2025-03-17)
        ///
        /// We need to resolve a chicken-and-egg bootsrapping paradox for Spaces and Resources.
        /// Currently to create a resource, it must be subset from an existing Space. Additionally,
        /// to create a Space, it must be Backed by either another ResourceSpace, or a SpaceBacking
        /// resource. This creates the bootstrapping paradox.
        ///
        /// One solution for this would be to create a special ResourceType Physical { 0 }, which
        /// does not need to be backed by anything, but I guess we would need one of these for
        /// every type of Physical Resource? (i.e. Physical Memory, Block Storage, ...). Maybe we
        /// just can't expect that every resource space is backed??
        ///
        /// Alternatively, we could use this unique ResourceType to define a Resource which does
        /// not need to be subset from a Resource space and bootsrap up that way.
        ///
        /// TODO Discuss this with @Reto
        ///
        /// Insert a MapEdge
        transition! {
            create_map_edge(me: MapEdgeR)
            {
            }
        }


        /// Create a ResourceSpace
        transition! {
            create_resource_space(space: ResourceSpace, backing: ResourceLike)
            {

            }
        }

        /// Remove a ResourceSpace
        ///
        /// Note (2025-03-17)
        ///
        /// Should this be an operation on a ResourceSpace which has already revoked all its
        /// allocations and Request edges, or should it rather operate as a recursive operation
        /// which deletes Resources and Request edges?
        ///
        transition! {
            destroy_resource_space(space: ResourceSpace)
            {

            }
        }


        // Inductiveness Proofs:

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(create_resource)]
        fn create_resource_inductive(pre: Self, post: Self, res: Resource, space: ResourceSpace, holder: ProtectionDomain)
        {
            // Invariant: hold_edge_to_each_resource
            assert forall |r: Resource| post.resources.contains(r) implies
                exists |e: HoldEdge| #[trigger] post.holds.contains(e) && e.dst() is Resource && e.dst()->res == r by {
                    let e = if (r == res) {
                        HoldEdge { src: holder, dst: ResourceLike::Resource { res }}
                    } else {
                        choose |e| #[trigger] pre.holds.contains(e) && e.dst() is Resource && e.dst()->res == r
                    };
                    assert(post.holds.contains(e) && e.dst() is Resource && e.dst()->res == r);
                }

            // Invariant: hold_edge_to_each_space
            assert forall |s: ResourceSpace| post.spaces.contains(s) implies
                exists |e: HoldEdge| #[trigger] post.holds.contains(e) && e.dst() is Space && e.dst()->space == s by {
                    let e = choose |e| #[trigger] pre.holds.contains(e) && e.dst() is Space && e.dst()->space == s;
                    assert(post.holds.contains(e) && e.dst() is Space && e.dst()->space == s);
                }

            // Invariant: resources_are_subsets
            assert forall |r: Resource| post.resources.contains(r) implies
                exists |e: SubsetEdge| #[trigger] post.subsets.contains(e) && e.src() == r by {
                    let e = if (r == res) {
                        SubsetEdge { src: res, dst: space }
                    } else {
                        choose |e| pre.subsets.contains(e) && #[trigger] e.src() == r
                    };
                    assert(post.subsets.contains(e) && e.src() == r);
                }
        }

        #[inductive(destroy_resource)]
        fn destroy_resource_inductive(pre: Self, post: Self, res: Resource)
        {
            // Invariant: hold_edge_to_each_resource
            assert forall |r: Resource| post.resources.contains(r) implies
                exists |e: HoldEdge| #[trigger] post.holds.contains(e) && e.dst() is Resource && e.dst()->res == r by {
                    let e = choose |e| #[trigger] pre.holds.contains(e) && e.dst() is Resource && e.dst()->res == r;
                    assert(post.holds.contains(e) && e.dst() is Resource && e.dst()->res == r);
                }

            // Invariant: hold_edge_to_each_space
            assert forall |s: ResourceSpace| post.spaces.contains(s) implies
                exists |e: HoldEdge| #[trigger] post.holds.contains(e) && e.dst() is Space && e.dst()->space == s by {
                    let e = choose |e| #[trigger] pre.holds.contains(e) && e.dst() is Space && e.dst()->space == s;
                    assert(post.holds.contains(e) && e.dst() is Space && e.dst()->space == s);
                }

            // Invariant subset_nodes_in_graph
            assert(post.subset_nodes_in_graph()) by {
                assert(forall |e| #[trigger] post.subsets.contains(e) ==> e.src() != res);
            }
        }

        #[inductive(create_pd)]
        fn create_pd_inductive(pre: Self, post: Self, pd: ProtectionDomain) { }

        #[inductive(destroy_pd)]
        fn destry_pd_inductve(pre: Self, post: Self, pd: ProtectionDomain) { }

        #[inductive(create_request_edge)]
        fn create_request_edge_inductive(pre: Self, post: Self, req: RequestEdge) { }

        #[inductive(destroy_request_edge)]
        fn destroy_request_edge_inductive(pre: Self, post: Self, req: RequestEdge) { }

        #[inductive(create_map_edge)]
        fn create_map_edge_inductive(pre: Self, post: Self, me: MapEdgeR) { }

        #[inductive(create_resource_space)]
        fn create_resource_space_inductive(pre: Self, post: Self, space: ResourceSpace, backing: ResourceLike) { }

        #[inductive(destroy_resource_space)]
        fn destroy_resource_space_inductive(pre: Self, post: Self, space: ResourceSpace) { }

        // Helper functions:

        }
    }

} // verus!
