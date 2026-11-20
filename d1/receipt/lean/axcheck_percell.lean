-- axcheck_percell.lean — axiom footprints of the D1C emission batches
-- (samples from receipt/lean/Percell77Fine.lean and Percell77RunLevel.lean;
--  the batches are self-contained core-Lean files, no imports).
set_option maxRecDepth 8000

-- representative FAIL line (fine level, row 77 window, first cell)
theorem percell77_fine_334254 : (1379373467 * 1000000000000000000 : Int) < (977166124357391793 * 516093837312000) := by decide
-- representative HOLD line (run level, the C1 high component)
theorem percell_run_C1_High_15 : (1 * 250000000000000000 : Int) ≥ (223013106678372741 * 1) := by decide
-- representative FAIL line (run level; mirrors the batch line byte-for-byte)
theorem percell_run_G3_rank_two_13 : (253438844523999567461371639857525695995105216506475714569 * 20000000000000000 : Int) < (10434910272290039 * 3213876088517980551083924184682325205044405987565585670602752) := by decide

#print axioms percell77_fine_334254
#print axioms percell_run_C1_High_15
#print axioms percell_run_G3_rank_two_13
