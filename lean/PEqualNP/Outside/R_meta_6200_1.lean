import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6200_1
    (oneReader : ∀ (D : Circuit), FanInTwo D → D.size ≤ 18 →
      (D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0))).length = 1 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (twoReaders : ∀ (D : Circuit), FanInTwo D → D.size ≤ 18 →
      (D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0))).length = 2 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (threeReaders : ∀ (D : Circuit), FanInTwo D → D.size ≤ 18 →
      (D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0))).length = 3 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.any fun (x6 : ℕ) => (List.ofFn x2).getD x6 (1 : Fin (10 : ℕ)) == (0 : Fin (10 : ℕ))) x1.gates).length ≤ (3 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ))]) ≠ (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) := by
  intro C σ hFan hSize hRead
  let ρ : ℕ → ℕ := fun i => if h : i < 10 then (σ ⟨i, h⟩).val else i
  let D : Circuit := ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ C.output⟩
  have hDFan : FanInTwo D := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hFan g0 hg0).1, by simp [(hFan g0 hg0).2]⟩
  have hDSize : D.size ≤ 18 := by
    change (C.gates.map (fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate))).length ≤ 18
    rw [List.length_map]
    exact hSize
  have hρEq : ∀ i : ℕ, ((List.ofFn σ).getD i (1 : Fin 10) == (0 : Fin 10)) = (ρ i == 0) := by
    intro i
    by_cases hi : i < 10
    · simp only [ρ, ↓reduceDIte, List.getD, List.getElem?_ofFn, hi, Option.getD_some]
      cases h0 : (σ ⟨i, hi⟩ == (0 : Fin 10))
      · have hne : (σ ⟨i, hi⟩).val ≠ 0 := by
          intro hv
          have : σ ⟨i, hi⟩ = 0 := Fin.ext hv
          simp [this] at h0
        simp [hne]
      · have heq : σ ⟨i, hi⟩ = 0 := eq_of_beq h0
        simp [heq]
    · have hge : (List.ofFn σ).length ≤ i := by simp; omega
      simp only [ρ, hi, ↓reduceDIte, List.getD, List.getElem?_eq_none hge, Option.getD_none]
      have hne : i ≠ 0 := by omega
      simp [hne]
  have hDRead : (D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0))).length =
      (C.gates.filter (fun g : Gate => g.inputs.any (fun i => (List.ofFn σ).getD i (1 : Fin 10) == (0 : Fin 10)))).length := by
    simp only [D, List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro g _
    simp only [Function.comp_apply, List.any_map]
    congr 1
    funext i
    exact (hρEq i).symm
  have hEval : ∀ x : Fin 10 → Bool,
      D.eval (List.ofFn x ++ [x 0 || x 2]) = C.eval (List.ofFn (x ∘ σ) ++ [x 0 || x 2]) := by
    intro x
    let step : List Bool → Gate → List Bool := fun w g =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hfold : ∀ (gs : List Gate) (wC wD : List Bool),
        wC.length = wD.length → 11 ≤ wC.length →
        (∀ i : ℕ, wC.getD i false = wD.getD (ρ i) false) →
        ((gs.map (fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate))).foldl step wD).getD (ρ C.output) false =
          (gs.foldl step wC).getD C.output false := by
      intro gs
      induction gs with
      | nil =>
        intro wC wD _ _ hagree
        exact (hagree C.output).symm
      | cons g gs ih =>
        intro wC wD hlen h11 hagree
        simp only [List.map_cons, List.foldl_cons]
        have hbit : g.op.eval ((g.inputs.map ρ).map fun i => wD.getD i false) =
            g.op.eval (g.inputs.map fun i => wC.getD i false) := by
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          exact (hagree i).symm
        apply ih (step wC g) (step wD ⟨g.op, g.inputs.map ρ⟩) (by simp [step, hlen]) (by simp [step]; omega)
        intro i
        by_cases hi : i < wC.length
        · have hρi : ρ i < wD.length := by
            dsimp only [ρ]
            split_ifs with h10
            · have := (σ ⟨i, h10⟩).isLt; omega
            · omega
          simp only [step, List.getD, List.getElem?_append_left hi, List.getElem?_append_left hρi]
          exact hagree i
        · have hge : wC.length ≤ i := Nat.le_of_not_lt hi
          have h10 : ¬ i < 10 := by omega
          have hρeq : ρ i = i := by simp [ρ, h10]
          rw [hρeq]
          rcases Nat.eq_or_lt_of_le hge with rfl | hgt
          · have h1 : (step wC g).getD wC.length false = g.op.eval (g.inputs.map fun i => wC.getD i false) := by
              simp [step, List.getD]
            have h2 : (step wD ⟨g.op, g.inputs.map ρ⟩).getD wD.length false =
                g.op.eval ((g.inputs.map ρ).map fun i => wD.getD i false) := by
              simp [step, List.getD]
            rw [h1, hlen, h2, hbit]
          · have hgtD : wD.length < i := hlen ▸ hgt
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i - wC.length ≠ 0)
            have hkD : i - wD.length = k + 1 := by omega
            simp only [step, List.getD, List.getElem?_append_right (Nat.le_of_lt hgt),
              List.getElem?_append_right (Nat.le_of_lt hgtD), hk, hkD,
              List.getElem?_cons_succ, List.getElem?_nil, Option.getD_none]
    apply hfold C.gates (List.ofFn (x ∘ σ) ++ [x 0 || x 2]) (List.ofFn x ++ [x 0 || x 2]) (by simp) (by simp)
    intro i
    by_cases h10 : i < 10
    · have hlt : (σ ⟨i, h10⟩).val < 10 := (σ ⟨i, h10⟩).isLt
      simp only [ρ, h10, ↓reduceDIte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simp [h10]), List.getElem?_append_left (by simp [hlt])]
      simp only [List.getElem?_ofFn, h10, hlt, ↓reduceDIte, Option.getD_some, Function.comp_apply]
    · simp only [ρ, h10, ↓reduceDIte]
      by_cases h11 : i = 10
      · subst h11
        simp [List.getD]
      · have hge1 : (List.ofFn (x ∘ σ) ++ [x 0 || x 2]).length ≤ i := by simp; omega
        have hge2 : (List.ofFn x ++ [x 0 || x 2]).length ≤ i := by simp; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
  have hDReadLe : (D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0))).length ≤ 3 := by
    omega
  rcases Nat.eq_zero_or_pos (D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0))).length with h0 | hpos
  · have hno0 : ∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≠ 0 := by
      have hemp : D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0)) = [] :=
        List.eq_nil_of_length_eq_zero h0
      intro g hg i hi hiz
      have hmem : g ∈ D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0)) := by
        rw [List.mem_filter]
        exact ⟨hg, List.any_eq_true.mpr ⟨i, hi, by simp [hiz]⟩⟩
      rw [hemp] at hmem
      cases hmem
    by_cases hout : D.output = 0
    · let a : Fin 10 → Bool := fun i => decide (i = 0)
      refine ⟨a, ?_⟩
      rw [← hEval a]
      have hda : D.eval (List.ofFn a ++ [a 0 || a 2]) = true := by
        have hpref : ∀ (gs : List Gate) (w : List Bool), 0 < w.length →
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD 0 false = w.getD 0 false := by
          intro gs
          induction gs with
          | nil => intro w _; rfl
          | cons g gs ih =>
            intro w hw
            rw [List.foldl_cons, ih _ (by simp)]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
        change (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn a ++ [a 0 || a 2])).getD D.output false = true
        rw [hout, hpref _ _ (by simp)]
        decide
      rw [hda]
      decide
    · let a : Fin 10 → Bool := fun i => decide (i = 2 ∨ i = 4)
      let b : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 2 ∨ i = 4)
      have hab : D.eval (List.ofFn a ++ [a 0 || a 2]) = D.eval (List.ofFn b ++ [b 0 || b 2]) := by
        let step : List Bool → Gate → List Bool := fun w g =>
          w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
        have hfold : ∀ (gs : List Gate) (wa wb : List Bool),
            (∀ g ∈ gs, ∀ i ∈ g.inputs, i ≠ 0) →
            wa.length = wb.length → (∀ i : ℕ, i ≠ 0 → wa.getD i false = wb.getD i false) →
            (gs.foldl step wa).getD D.output false = (gs.foldl step wb).getD D.output false := by
          intro gs
          induction gs with
          | nil => intro wa wb _ _ hne; exact hne D.output hout
          | cons g gs ih =>
            intro wa wb hno hlen hne
            simp only [List.foldl_cons]
            have hbit : g.op.eval (g.inputs.map fun i => wa.getD i false) =
                g.op.eval (g.inputs.map fun i => wb.getD i false) := by
              congr 1
              apply List.map_congr_left
              intro i hi
              exact hne i (hno g List.mem_cons_self i hi)
            apply ih (step wa g) (step wb g) (fun g' hg' => hno g' (List.mem_cons_of_mem g hg'))
              (by simp [step, hlen])
            intro i hi
            by_cases hlt : i < wa.length
            · have hltb : i < wb.length := hlen ▸ hlt
              simp only [step, List.getD, List.getElem?_append_left hlt, List.getElem?_append_left hltb]
              exact hne i hi
            · have hge : wa.length ≤ i := Nat.le_of_not_lt hlt
              rcases Nat.eq_or_lt_of_le hge with rfl | hgt
              · have h1 : (step wa g).getD wa.length false = g.op.eval (g.inputs.map fun i => wa.getD i false) := by
                  simp [step, List.getD]
                have h2 : (step wb g).getD wb.length false = g.op.eval (g.inputs.map fun i => wb.getD i false) := by
                  simp [step, List.getD]
                rw [h1, hlen, h2, hbit]
              · have hgtb : wb.length < i := hlen ▸ hgt
                obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i - wa.length ≠ 0)
                have hkb : i - wb.length = k + 1 := by omega
                simp only [step, List.getD, List.getElem?_append_right (Nat.le_of_lt hgt),
                  List.getElem?_append_right (Nat.le_of_lt hgtb), hk, hkb,
                  List.getElem?_cons_succ, List.getElem?_nil, Option.getD_none]
        apply hfold D.gates (List.ofFn a ++ [a 0 || a 2]) (List.ofFn b ++ [b 0 || b 2]) hno0 (by simp)
        intro i hi
        by_cases h11 : i < 11
        · interval_cases i
          · exact absurd rfl hi
          all_goals decide
        · have hge1 : (List.ofFn a ++ [a 0 || a 2]).length ≤ i := by simp; omega
          have hge2 : (List.ofFn b ++ [b 0 || b 2]).length ≤ i := by simp; omega
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
      by_cases hda : D.eval (List.ofFn a ++ [a 0 || a 2]) = false
      · refine ⟨b, ?_⟩
        rw [← hEval b, ← hab, hda]
        decide
      · refine ⟨a, ?_⟩
        rw [← hEval a]
        intro heq
        exact hda (heq.trans (by decide))
  · have hcases : (D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0))).length = 1 ∨
        (D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0))).length = 2 ∨
        (D.gates.filter (fun g : Gate => g.inputs.any (fun i => i == 0))).length = 3 := by omega
    rcases hcases with h1 | h2 | h3
    · obtain ⟨x, hx⟩ := oneReader D hDFan hDSize h1
      exact ⟨x, by rwa [← hEval x]⟩
    · obtain ⟨x, hx⟩ := twoReaders D hDFan hDSize h2
      exact ⟨x, by rwa [← hEval x]⟩
    · obtain ⟨x, hx⟩ := threeReaders D hDFan hDSize h3
      exact ⟨x, by rwa [← hEval x]⟩
