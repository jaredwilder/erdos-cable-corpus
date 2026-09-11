set_option autoImplicit false

structure PacketInventory where (lemmaJsons : Nat) (quantities : Nat) (bounds : Nat) (comparators : Nat) (signs : Nat) (foreignRefutations : Nat) (runTranscripts : Nat) (artifactsBoundToS : Nat)

def L1_inventory : PacketInventory :=
  { lemmaJsons := 1, quantities := 0, bounds := 0, comparators := 0, signs := 0,
    foreignRefutations := 6, runTranscripts := 0, artifactsBoundToS := 0 }

def check_L1 (inv : PacketInventory) : Bool :=
  inv.lemmaJsons == 1
  && inv.quantities == 0 && inv.bounds == 0
  && inv.comparators == 0 && inv.signs == 0
  && inv.foreignRefutations == 6
  && inv.runTranscripts == 0
  && inv.artifactsBoundToS == 0

theorem msl_fmz_erdos1137_campaign_001_R001_L1  : check_L1 L1_inventory = true := by decide
