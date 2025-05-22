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

        pub open spec fn new(l1: int, l2: int) -> Self {
            CapAddr { l1, l2 }
        }

        /// Extracts the slot (L2 index) from this capability address
        pub open spec fn get_slot(&self) -> CapSlot {
            CapSlot::new(self.l2)
        }

        /// Extracts the CNode address component from this capability address 
        pub open spec fn get_cnode_addr(&self) -> CapAddr {
            CapAddr::new(self.l1, 0)
        }
    }

    pub ghost struct CapSlot {
        pub slot: int,
    }

    impl CapSlot {
        pub open spec fn wf(&self) -> bool {
            0 <= self.slot <= U8_MAX
        }

        pub open spec fn new(slot: int) -> Self {
            CapSlot { slot }
        }
    }

    /// The CNode type, either the rootcn/L1CNode (0) or a L2CNode (1)
    pub ghost enum CNodeType {
        L1,
        L2,
        Cap,
    }

    /// User-level representation of a CNode
    pub ghost struct CNodeRef {
        pub croot: CapAddr,
        pub cnode: CapAddr,
        pub level: CNodeType,
    }

    //pub spec const CNODE_NULL: CNodeRef = CNodeRef { level: CNodeTypeRoot }; 

    // List of well known cnodes #todo(Instantiate them correctly)
    impl CNodeRef {
        pub open spec fn wf(&self) -> bool {
            self.croot.wf() && self.cnode.wf() && self.level != CNodeType::Cap
        }

        pub open spec fn new(croot: CapAddr, cnode: CapAddr, level: CNodeType) -> Self {
            CNodeRef { croot, cnode, level }
        }

        /// Checks whether the CNodeRef is NULL
        pub open spec fn is_null(&self) -> bool {
            self.croot == CPTR_ZERO && self.cnode == CPTR_ZERO
        }

        /// Compares two CNodeRefs returning true if they're equal
        pub open spec fn cmp(c1: &Self, c2: &Self) -> bool {
            c1.cnode == c2.cnode && c1.croot == c2.croot && c1.level == c2.level  
        }
    }

    /// User-level representation of a Capability
    pub ghost struct CapRef {
        /// The CNode in which this Capability lives
        pub cnode: CNodeRef,
        /// Slot within the CNode
        pub slot: CapSlot,
    }

    impl CapRef {
        pub open spec fn wf(&self) -> bool {
            self.cnode.wf() && self.slot.wf()
        }

        pub open spec fn new(cnode: CNodeRef, slot: CapSlot) -> Self {
            CapRef { cnode, slot }
        }

        /// Checks whether the CapRef is NULL
        pub open spec fn is_null(&self) -> bool {
            self.cnode.is_null() && self.slot == CSLOT_ZERO
        }

        /// Compares two CapRefs returning true if they're equal
        pub open spec fn cmp(c1: &Self, c2: &Self) -> bool {
            c1.cnode == c2.cnode && c1.slot == c2.slot
        }

        /// Returns the depth in the CSpace address of a capability
        pub open spec fn get_cap_level(&self) -> CNodeType
            recommends self.wf()
        {
            if (self.is_null()) {
                CNodeType::L1
            } else {
                match self.cnode.level {
                    CNodeType::L1 => CNodeType::L2,
                    CNodeType::L2 => CNodeType::Cap,
                    // TODO(Talk to Reto, is this the right way to do this?)
                    CNodeType::Cap => arbitrary(),
                }
            }   
        }

        /// Returns the depth in the CSpace address of the CNode containing this capability
        pub open spec fn get_cnode_level(&self) -> CNodeType {
            self.cnode.level
        }
        
        /// Returns the CapAddr of this capability
        pub open spec fn get_capaddr(&self) -> CapAddr {
            if (self.is_null()) {
                CPTR_ZERO
            } else {
                match self.cnode.level {
                    CNodeType::L1 => CapAddr::new(self.slot.slot, 0),
                    CNodeType::L2 => CapAddr::new(self.cnode.cnode.l1, self.cnode.cnode.l2 + self.slot.slot),
                    _ => {
                        // TODO(Talk to Reto, is this the right way to do this?)
                        // This should never happen
                        arbitrary()
                    }
                }
            }
        }

        /// Returns the CapAddr of the CNode containing this capability
        pub open spec fn get_cnode_addr(&self) -> CapAddr {
            match self.cnode.level {
                CNodeType::L1 => self.cnode.croot,
                CNodeType::L2 => self.cnode.cnode,
                _ => {
                    // TODO(Talk to Reto, is this the right way to do this?)
                    // This should never happen
                    arbitrary()
                }
            }
        }

        /// Returns the CapAddr of the CSpace Root Cap of this capability
        pub open spec fn get_croot_addr(&self) -> CapAddr {
            self.cnode.croot
        }

        /// Returns the CapRef of the CSpace Root Cap of this capability
        pub open spec fn get_croot_capref(&self) -> CapRef {
            let croot = self.get_croot_addr();
            CapRef::new(CNodeRef::new(CPTR_ROOTCN, croot, CNodeType::L2), croot.get_slot())
        }

    }


    //////////////////////////////////////////////////////////////////////
    /// Well known constants
    //////////////////////////////////////////////////////////////////////


    /// TaskCNode slot in the Root CNode
    pub spec const ROOTCN_SLOT_TASKCN: int = 0;
    /// PageCNode slot in the Root CNode
    pub spec const ROOTCN_SLOT_PAGECN: int = 1;
    /// Slot for a CNode of BASE_PAGE_SIZE frames
    pub spec const ROOTCN_SLOT_BASE_PAGE_CN: int = 2;
    /// Slot for a CNode of SUPER frames
    pub spec const ROOTCN_SLOT_SUPERCN: int = 3;
    /// SegmentCNode slot in the Root CNode
    pub spec const ROOTCN_SLOT_SEGCN: int = 4;
    /// PhysAddrCNode slot in the Root CNode
    pub spec const ROOTCN_SLOT_PACN: int = 5;
    /// Multiboot Modules CNode slot in the Root CNode
    pub spec const ROOTCN_SLOT_MODULECN: int = 6;
    /// Slot used for base CNode slot allocator in early code
    pub spec const ROOTCN_SLOT_SLOT_ALLOC0: int = 7;
    /// Root of slot allocator 1
    pub spec const ROOTCN_SLOT_SLOT_ALLOC1: int = 8;
    /// Root of slot allocator 2
    pub spec const ROOTCN_SLOT_SLOT_ALLOC2: int = 9;
    /// Slot for a CNode for the root VNode mappings
    pub spec const ROOTCN_SLOT_ROOT_MAPPING: int = 10;
    /// ArgCNode slot in the Root CNode
    pub spec const ROOTCN_SLOT_ARGCN: int = 11;
    /// BSP KCB cap to fix reverse lookup issues
    pub spec const ROOTCN_SLOT_BSPKCB: int = 12;
    /// Slot for a CNode of L2_CNODE_SIZE frames
    pub spec const ROOTCN_SLOT_EARLY_CN_CN: int = 13;
    /// First free slot in the Root CNode for user
    pub spec const ROOTCN_SLOTS_USER: int = 14;
    /// TaskCNode in itself (XXX)
    pub spec const TASKCN_SLOT_TASKCN: int = 0;
    /// Dispatcher cap in Task CNode
    pub spec const TASKCN_SLOT_DISPATCHER: int = 1;
    /// RootCNode slot in Task CNode
    pub spec const TASKCN_SLOT_ROOTCN: int = 2;
    /// Dispatcher frame cap in Task CNode
    pub spec const TASKCN_SLOT_DISPFRAME: int = 4;
    /// IRQ cap in Task CNode
    pub spec const TASKCN_SLOT_IRQ: int = 5;
    /// IO cap in Task CNode
    pub spec const TASKCN_SLOT_DEV: int = 6;
    /// Bootinfo frame slot in Task CNode
    pub spec const TASKCN_SLOT_BOOTINFO: int = 7;
    /// Kernel cap in Task CNode
    pub spec const TASKCN_SLOT_KERNELCAP: int = 8;
    /// Trace buffer cap in Task CNode
    pub spec const TASKCN_SLOT_TRACEBUF: int = 9;
    /// Cap for the page containing a list of command line arguments
    pub spec const TASKCN_SLOT_ARGSPAGE: int = 10;
    /// Frame cap for URPC communication
    pub spec const TASKCN_SLOT_MON_URPC: int = 11;
    /// Session ID the domain belongs to
    pub spec const TASKCN_SLOT_SESSIONID: int = 12;
    /// Cap for inherited file descriptors
    pub spec const TASKCN_SLOT_FDSPAGE: int = 13;
    /// Cap for performance monitoring
    pub spec const TASKCN_SLOT_PERF_MON: int = 14;
    /// System memory cap (purpose unclear)
    pub spec const TASKCN_SLOT_SYSMEM: int = 15;
    /// Copy of realmode section used to bootstrap a core
    pub spec const TASKCN_SLOT_COREBOOT: int = 16;
    /// Copy of IPI cap
    pub spec const TASKCN_SLOT_IPI: int = 17;
    /// Cap for the process manager
    pub spec const TASKCN_SLOT_PROC_MNG: int = 18;
    /// Domain ID cap
    pub spec const TASKCN_SLOT_DOMAINID: int = 19;
    /// DeviceID manager capability
    pub spec const TASKCN_SLOT_DEVMAN: int = 20;
    /// Memory for early allocation
    pub spec const TASKCN_SLOT_EARLYMEM: int = 21;
    /// First free slot in Task CNode for user
    pub spec const TASKCN_SLOTS_USER: int = 22;


    /// Generic 0 Slot CapAddr, used in Null checks
    pub spec const CPTR_ZERO: CapAddr = CapAddr::new(0, 0);
    /// CapAddr of the Task CNode
    pub spec const CPTR_TASKCN_BASE: CapAddr = CapAddr::new(ROOTCN_SLOT_TASKCN, TASKCN_SLOT_TASKCN);
    /// CapAddr of the Super CNode Base
    pub spec const CPTR_SUPERCN_BASE: CapAddr = CapAddr::new(ROOTCN_SLOT_SUPERCN, 0);
    /// CapAddr of the Page CNode Base
    pub spec const CPTR_PAGECN_BASE: CapAddr = CapAddr::new(ROOTCN_SLOT_PAGECN, 0);
    /// CapAddr of Module CNode Base
    pub spec const CPTR_MODULECN_BASE: CapAddr = CapAddr::new(ROOTCN_SLOT_MODULECN, 0);
    /// CapAddr of Root CNode
    pub spec const CPTR_ROOTCN: CapAddr = CapAddr::new(ROOTCN_SLOT_TASKCN, TASKCN_SLOT_ROOTCN);

    /// Generic 0 Slot CapSlot, used in Null checks
    pub spec const CSLOT_ZERO: CapSlot = CapSlot::new(0);


    pub spec const CNODE_NODE: CNodeRef =   CNodeRef::new(CPTR_ZERO,   CPTR_ZERO,           CNodeType::L1);
    pub spec const CNODE_ROOT: CNodeRef =   CNodeRef::new(CPTR_ROOTCN, CPTR_ZERO,           CNodeType::L1);
    pub spec const CNODE_TASK: CNodeRef =   CNodeRef::new(CPTR_ROOTCN, CPTR_TASKCN_BASE,    CNodeType::L2);
    pub spec const CNODE_MEMORY: CNodeRef = CNodeRef::new(CPTR_ROOTCN, CPTR_SUPERCN_BASE,   CNodeType::L2);
    pub spec const CNODE_PAGE: CNodeRef =   CNodeRef::new(CPTR_ROOTCN, CPTR_PAGECN_BASE,    CNodeType::L2);
    pub spec const CNODE_MODULE: CNodeRef = CNodeRef::new(CPTR_ROOTCN, CPTR_MODULECN_BASE,  CNodeType::L2);

}
