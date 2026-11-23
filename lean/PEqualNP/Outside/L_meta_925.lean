import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds

def stepWires (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma stepWires_length (w : List Bool) (g : Gate) :
    (stepWires w g).length = w.length + 1 := by
  simp [stepWires]

lemma foldl_stepWires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWires w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, stepWires_length]
    omega

lemma getD_append_lt (w₁ w₂ : List Bool) {i : ℕ} (hi : i < w₁.length) :
    (w₁ ++ w₂).getD i false = w₁.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_stepWires_getD_lt (gs : List Gate) (w : List Bool) {u : ℕ} (hu : u < w.length) :
    (gs.foldl stepWires w).getD u false = w.getD u false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepWires w g) (by rw [stepWires_length]; omega)]
    exact getD_append_lt w _ hu

lemma getD_eq_false_of_le (w : List Bool) {u : ℕ} (hu : w.length ≤ u) :
    w.getD u false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hu]

def wireAt (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (gs.foldl stepWires (List.ofFn x)).getD u false

lemma wireAt_eq_eval (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (u : ℕ) :
    Circuit.eval ⟨gs, u⟩ (List.ofFn x) = wireAt gs n x u :=
  rfl

lemma wireAt_lt_length (gs : List Gate) (n : ℕ) (x : Fin n → Bool) {u : ℕ}
    (hu : wireAt gs n x u = true) : u < n + gs.length := by
  by_contra h
  have hle : (gs.foldl stepWires (List.ofFn x)).length ≤ u := by
    rw [foldl_stepWires_length, List.length_ofFn]
    omega
  have hf : wireAt gs n x u = false := getD_eq_false_of_le _ hle
  rw [hf] at hu
  exact Bool.false_ne_true hu

lemma wireAt_input (gs : List Gate) (n : ℕ) (x : Fin n → Bool) {u : ℕ} (hu : u < n) :
    wireAt gs n x u = x ⟨u, hu⟩ := by
  unfold wireAt
  rw [foldl_stepWires_getD_lt gs (List.ofFn x) (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma foldl_stepWires_getD_add (gs : List Gate) (w : List Bool) {j : ℕ} (hj : j < gs.length) :
    (gs.foldl stepWires w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun a =>
        if a < w.length + j then (gs.foldl stepWires w).getD a false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero, List.foldl_cons]
      rw [foldl_stepWires_getD_lt gs (stepWires w g) (by rw [stepWires_length]; omega)]
      have hget : (stepWires w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWires, List.getD_eq_getElem?_getD]
      rw [hget]
      congr 1
      apply List.map_congr_left
      intro a _
      by_cases ha : a < w.length
      · simp only [ha, ↓reduceIte]
        rw [foldl_stepWires_getD_lt gs (stepWires w g) (by rw [stepWires_length]; omega)]
        exact (getD_append_lt w _ ha).symm
      · simp only [ha, ↓reduceIte]
        exact getD_eq_false_of_le w (Nat.le_of_not_lt ha)
    | succ k =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have hk : k < gs.length := by simpa using hj
      have hlen : (stepWires w g).length = w.length + 1 := stepWires_length w g
      have heq : w.length + (k + 1) = (stepWires w g).length + k := by omega
      rw [heq]
      exact ih (stepWires w g) hk

lemma wireAt_gate (gs : List Gate) (n : ℕ) (x : Fin n → Bool) {j : ℕ} (hj : j < gs.length) :
    wireAt gs n x (n + j) =
      gs[j].op.eval (gs[j].inputs.map fun a =>
        if a < n + j then wireAt gs n x a else false) := by
  unfold wireAt
  have h := foldl_stepWires_getD_add gs (List.ofFn x) hj
  simpa [List.length_ofFn] using h

lemma foldl_stepWires_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w₁ w₂ : List Bool) (hlen : w₁.length = w₂.length)
    (hle : ∀ i, w₁.getD i false = true → w₂.getD i false = true) :
    ∀ i, (gs.foldl stepWires w₁).getD i false = true →
      (gs.foldl stepWires w₂).getD i false = true := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hle
  | cons g gs ih =>
    intro i hi
    simp only [List.foldl_cons] at hi ⊢
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (List.mem_cons_self ..)
    have hgs' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    have hstep : g.op.eval (g.inputs.map fun k => w₁.getD k false) = true →
        g.op.eval (g.inputs.map fun k => w₂.getD k false) = true := by
      rcases hg with hop | hop
      · rw [hop]
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂]
        intro h k hk
        exact hle k (h k hk)
      · rw [hop]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
        rintro ⟨k, hk, hkw⟩
        exact ⟨k, hk, hle k hkw⟩
    refine ih hgs' (stepWires w₁ g) (stepWires w₂ g) ?_ ?_ i hi
    · simp [stepWires_length, hlen]
    · intro k hk
      by_cases hlt : k < w₁.length
      · unfold stepWires at hk ⊢
        rw [getD_append_lt w₁ _ hlt] at hk
        rw [getD_append_lt w₂ _ (hlen ▸ hlt)]
        exact hle k hk
      · by_cases heq : k = w₁.length
        · subst heq
          simp only [stepWires, List.getD_eq_getElem?_getD] at hk ⊢
          rw [List.getElem?_concat_length] at hk
          rw [hlen, List.getElem?_concat_length]
          simp only [Option.getD_some] at hk ⊢
          exact hstep (by simpa [List.getD_eq_getElem?_getD] using hk)
        · have hge : (stepWires w₁ g).length ≤ k := by
            rw [stepWires_length]
            omega
          rw [getD_eq_false_of_le _ hge] at hk
          exact False.elim (Bool.false_ne_true hk)

lemma wireAt_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (u : ℕ) (hu : wireAt gs n x u = true) :
    wireAt gs n y u = true := by
  refine foldl_stepWires_mono gs hgs (List.ofFn x) (List.ofFn y) (by simp) ?_ u hu
  intro i hi
  by_cases hlt : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true,
      Option.getD_some] at hi ⊢
    exact hxy ⟨i, hlt⟩ hi
  · have hge : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_lt hlt
    rw [getD_eq_false_of_le _ hge] at hi
    exact False.elim (Bool.false_ne_true hi)

def ind {n : ℕ} (T : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ T)

lemma weight_ind {n : ℕ} (T : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin n => ind T i = true)).card = T.card := by
  have h : Finset.univ.filter (fun i : Fin n => ind T i = true) = T := by
    ext i
    simp [ind]
  rw [h]

def spec (gates : List Gate) {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m) :
    Finset (Fin gates.length) :=
  Finset.univ.filter fun j =>
    wireAt gates n (ind (S w)) (n + j.1) = true ∧
      ∀ v : Fin m, v ≠ w → wireAt gates n (ind (S v)) (n + j.1) = false

lemma spec_disjoint (gates : List Gate) {n m : ℕ} (S : Fin m → Finset (Fin n))
    {w₁ w₂ : Fin m} (hw : w₁ ≠ w₂) :
    Disjoint (spec gates S w₁) (spec gates S w₂) := by
  rw [Finset.disjoint_left]
  intro j hj₁ hj₂
  simp only [spec, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
  have ht := hj₁.1
  have hf := hj₂.2 w₁ hw
  rw [ht] at hf
  exact Bool.false_ne_true hf.symm

def GoodState (n K q : ℕ) {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (w : Fin m) (B : ℕ) (F : Finset ℕ) (P : Finset (Fin n))
    (A : Finset (Fin gates.length)) (d : ℕ) : Prop :=
  (∀ u ∈ F, u < B) ∧
  (∀ u ∈ F, wireAt gates n (ind (S w)) u = true) ∧
  (∀ x : Fin n → Bool,
    (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
    (∀ p ∈ P, x p = true) →
    (∃ v ∈ S w, x v = false) →
    ∃ u ∈ F, wireAt gates n x u = false) ∧
  A ⊆ spec gates S w ∧
  F.card + d ≤ 1 + A.card ∧
  (∀ u ∈ F, ∀ j ∈ A, u < n + j.1) ∧
  (P ∩ S w).card ≤ d ∧
  (P.card ≤ d ∨ (P.card ≤ d * q + 1 ∧ ∃ v₀ : Fin m, S v₀ ⊆ P))

lemma empty_contradiction (q n m K : ℕ) (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hcardS : ∀ i : Fin m, (S i).card = q + 1)
    (gates : List Gate) (w : Fin m) (c : ℕ) (hcq : c ≤ q) (hcK : c * q < K)
    (hspec : (spec gates S w).card < c)
    (P : Finset (Fin n)) (A : Finset (Fin gates.length)) (d : ℕ)
    (hgs : GoodState n K q S gates w 0 ∅ P A d) : False := by
  rcases hgs with ⟨_, _, hFalse, hAsub, hCard, _, hHit, hSize⟩
  have hd_le_c : d ≤ c := by
    have h1 := Finset.card_le_card hAsub
    simp only [Finset.card_empty, Nat.zero_add] at hCard
    omega
  have hP_le_K : P.card ≤ K := by
    rcases hSize with hPd | ⟨hPdq, _⟩
    · have h1 : d ≤ d * q := Nat.le_mul_of_pos_right d (by omega)
      have h2 : d * q ≤ c * q := Nat.mul_le_mul_right q hd_le_c
      omega
    · have h2 : d * q ≤ c * q := Nat.mul_le_mul_right q hd_le_c
      omega
  have hex : ∃ v ∈ S w, ind P v = false := by
    by_contra hno
    push Not at hno
    have hsub : S w ⊆ P := by
      intro v hv
      have hv' := hno v hv
      simp [ind] at hv'
      exact hv'
    have hinter_eq : P ∩ S w = S w := Finset.inter_eq_right.mpr hsub
    have hcard_eq : (P ∩ S w).card = q + 1 := by
      rw [hinter_eq, hcardS w]
    omega
  have hw_le : (Finset.univ.filter (fun i : Fin n => ind P i = true)).card ≤ K := by
    rw [weight_ind]
    exact hP_le_K
  have hp_all : ∀ p ∈ P, ind P p = true := by
    intro p hp
    simp [ind, hp]
  obtain ⟨u, hu, _⟩ := hFalse (ind P) hw_le hp_all hex
  simp at hu

lemma descent_contradiction (q n m K : ℕ) (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hcardS : ∀ i : Fin m, (S i).card = q + 1)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin m) (c : ℕ) (hcq : c ≤ q) (hcK : c * q < K)
    (hspec : (spec gates S w).card < c) :
    ∀ B F P A d, GoodState n K q S gates w B F P A d → False := by
  intro B
  induction B using Nat.strong_induction_on with
  | ind B ih =>
    intro F P A d hgs
    by_cases hF : F.Nonempty
    · let u := F.max' hF
      have huF : u ∈ F := F.max'_mem hF
      have huB : u < B := hgs.1 u huF
      have hu_true : wireAt gates n (ind (S w)) u = true := hgs.2.1 u huF
      have hu_lt_len : u < n + gates.length := wireAt_lt_length gates n (ind (S w)) hu_true
      have hErLt : ∀ y ∈ F.erase u, y < u := by
        intro y hy
        rw [Finset.mem_erase] at hy
        exact lt_of_le_of_ne (F.le_max' y hy.2) hy.1
      rcases hgs with ⟨_, hTrue, hFalse, hAsub, hCard, hOrder, hHit, hSize⟩
      have hgs_op : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg => (hgates g hg).1
      by_cases hun : u < n
      · let i : Fin n := ⟨u, hun⟩
        have hwi : ∀ x : Fin n → Bool, wireAt gates n x u = x i :=
          fun x => wireAt_input gates n x hun
        have hiSw : i ∈ S w := by
          have h1 := hu_true
          rw [hwi (ind (S w))] at h1
          simpa [ind] using h1
        by_cases hiP : i ∈ P
        · refine ih u huB (F.erase u) P A d ⟨hErLt, ?_, ?_, hAsub, ?_, ?_, hHit, hSize⟩
          · intro y hy
            exact hTrue y (Finset.erase_subset u F hy)
          · intro x hxK hxP hxSw
            obtain ⟨f, hfF, hfx⟩ := hFalse x hxK hxP hxSw
            refine ⟨f, Finset.mem_erase.mpr ⟨?_, hfF⟩, hfx⟩
            intro hfu
            rw [hfu, hwi x, hxP i hiP] at hfx
            exact Bool.false_ne_true hfx.symm
          · have hle : (F.erase u).card ≤ F.card := Finset.card_erase_le
            omega
          · intro y hy j hj
            exact hOrder y (Finset.erase_subset u F hy) j hj
        · refine ih u huB (F.erase u) (insert i P) A (d + 1)
            ⟨hErLt, ?_, ?_, hAsub, ?_, ?_, ?_, ?_⟩
          · intro y hy
            exact hTrue y (Finset.erase_subset u F hy)
          · intro x hxK hxP hxSw
            have hxP' : ∀ p ∈ P, x p = true :=
              fun p hp => hxP p (Finset.mem_insert_of_mem hp)
            obtain ⟨f, hfF, hfx⟩ := hFalse x hxK hxP' hxSw
            refine ⟨f, Finset.mem_erase.mpr ⟨?_, hfF⟩, hfx⟩
            intro hfu
            rw [hfu, hwi x, hxP i (Finset.mem_insert_self i P)] at hfx
            exact Bool.false_ne_true hfx.symm
          · have h1 : (F.erase u).card + 1 = F.card := Finset.card_erase_add_one huF
            omega
          · intro y hy j hj
            exact hOrder y (Finset.erase_subset u F hy) j hj
          · have hsub : insert i P ∩ S w ⊆ insert i (P ∩ S w) := by
              intro z hz
              simp only [Finset.mem_inter, Finset.mem_insert] at hz ⊢
              rcases hz.1 with rfl | hzP
              · exact Or.inl rfl
              · exact Or.inr ⟨hzP, hz.2⟩
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_insert_le i (P ∩ S w)
            omega
          · rcases hSize with hPd | ⟨hPdq, v₀, hv₀⟩
            · left
              have h1 := Finset.card_insert_le i P
              omega
            · right
              refine ⟨?_, v₀, hv₀.trans (Finset.subset_insert i P)⟩
              have h1 := Finset.card_insert_le i P
              have h2 : (d + 1) * q + 1 = d * q + q + 1 := by ring
              omega
      · have hnu : n ≤ u := Nat.le_of_not_lt hun
        let j : Fin gates.length := ⟨u - n, by omega⟩
        have huj : u = n + j.1 := (Nat.add_sub_cancel' hnu).symm
        by_cases hspec_j : ∀ v : Fin m, v ≠ w → wireAt gates n (ind (S v)) u = false
        · have hj_spec : j ∈ spec gates S w := by
            simp only [spec, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨huj ▸ hu_true, fun v hv => huj ▸ hspec_j v hv⟩
          have hj_not_A : j ∉ A := by
            intro hjA
            have hlt := hOrder u huF j hjA
            rw [huj] at hlt
            exact absurd hlt (Nat.lt_irrefl _)
          let g := gates[j.1]
          have hg_mem : g ∈ gates := List.getElem_mem j.2
          have hg := hgates g hg_mem
          have hgate_eval : ∀ x : Fin n → Bool,
              wireAt gates n x u =
                g.op.eval (g.inputs.map fun a => if a < u then wireAt gates n x a else false) := by
            intro x
            rw [huj]
            exact wireAt_gate gates n x j.2
          rcases hg.1 with hop | hop
          · rcases hinputs : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · refine ih u huB (F.erase u) P A d ⟨hErLt, ?_, ?_, hAsub, ?_, ?_, hHit, hSize⟩
              · intro y hy
                exact hTrue y (Finset.erase_subset u F hy)
              · intro x hxK hxP hxSw
                obtain ⟨f, hfF, hfx⟩ := hFalse x hxK hxP hxSw
                refine ⟨f, Finset.mem_erase.mpr ⟨?_, hfF⟩, hfx⟩
                intro hfu
                have htrue : wireAt gates n x u = true := by
                  rw [hgate_eval x, hop, hinputs]
                  rfl
                rw [hfu, htrue] at hfx
                exact Bool.false_ne_true hfx.symm
              · have hle : (F.erase u).card ≤ F.card := Finset.card_erase_le
                omega
              · intro y hy k hk
                exact hOrder y (Finset.erase_subset u F hy) k hk
            · have ha_eval : ∀ x : Fin n → Bool,
                  wireAt gates n x u = if a < u then wireAt gates n x a else false := by
                intro x
                rw [hgate_eval x, hop, hinputs]
                simp [GateOp.eval]
              have ha_lt : a < u := by
                have h1 := ha_eval (ind (S w))
                rw [hu_true] at h1
                by_contra hno
                simp only [hno, ↓reduceIte] at h1
                exact Bool.false_ne_true h1.symm
              have ha_true : wireAt gates n (ind (S w)) a = true := by
                have h1 := ha_eval (ind (S w))
                simp only [hu_true, ha_lt, ↓reduceIte] at h1
                exact h1.symm
              refine ih u huB (insert a (F.erase u)) P A d
                ⟨?_, ?_, ?_, hAsub, ?_, ?_, hHit, hSize⟩
              · intro y hy
                rw [Finset.mem_insert] at hy
                rcases hy with rfl | hy
                · exact ha_lt
                · exact hErLt y hy
              · intro y hy
                rw [Finset.mem_insert] at hy
                rcases hy with rfl | hy
                · exact ha_true
                · exact hTrue y (Finset.erase_subset u F hy)
              · intro x hxK hxP hxSw
                obtain ⟨f, hfF, hfx⟩ := hFalse x hxK hxP hxSw
                by_cases hfu : f = u
                · subst hfu
                  refine ⟨a, Finset.mem_insert_self a _, ?_⟩
                  have h1 := ha_eval x
                  simp only [ha_lt, ↓reduceIte] at h1
                  rw [← h1, hfx]
                · exact ⟨f, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hfu, hfF⟩), hfx⟩
              · have h1 : (insert a (F.erase u)).card ≤ (F.erase u).card + 1 :=
                  Finset.card_insert_le a (F.erase u)
                have h2 : (F.erase u).card + 1 = F.card := Finset.card_erase_add_one huF
                omega
              · intro y hy k hk
                rw [Finset.mem_insert] at hy
                rcases hy with rfl | hy
                · exact lt_trans ha_lt (hOrder u huF k hk)
                · exact hOrder y (Finset.erase_subset u F hy) k hk
            · have hab_eval : ∀ x : Fin n → Bool,
                  wireAt gates n x u =
                    ((if a < u then wireAt gates n x a else false) &&
                      (if b < u then wireAt gates n x b else false)) := by
                intro x
                rw [hgate_eval x, hop, hinputs]
                simp [GateOp.eval]
              have hab_w := hab_eval (ind (S w))
              rw [hu_true] at hab_w
              have ha_branch : (if a < u then wireAt gates n (ind (S w)) a else false) = true := by
                exact Bool.and_elim_left hab_w.symm
              have hb_branch : (if b < u then wireAt gates n (ind (S w)) b else false) = true := by
                exact Bool.and_elim_right hab_w.symm
              have ha_lt : a < u := by
                by_contra hno
                simp only [hno, ↓reduceIte] at ha_branch
                exact Bool.false_ne_true ha_branch
              have hb_lt : b < u := by
                by_contra hno
                simp only [hno, ↓reduceIte] at hb_branch
                exact Bool.false_ne_true hb_branch
              have ha_true : wireAt gates n (ind (S w)) a = true := by
                simp only [ha_lt, ↓reduceIte] at ha_branch
                exact ha_branch
              have hb_true : wireAt gates n (ind (S w)) b = true := by
                simp only [hb_lt, ↓reduceIte] at hb_branch
                exact hb_branch
              refine ih u huB (insert a (insert b (F.erase u))) P (insert j A) d
                ⟨?_, ?_, ?_, ?_, ?_, ?_, hHit, hSize⟩
              · intro y hy
                simp only [Finset.mem_insert] at hy
                rcases hy with rfl | rfl | hy
                · exact ha_lt
                · exact hb_lt
                · exact hErLt y hy
              · intro y hy
                simp only [Finset.mem_insert] at hy
                rcases hy with rfl | rfl | hy
                · exact ha_true
                · exact hb_true
                · exact hTrue y (Finset.erase_subset u F hy)
              · intro x hxK hxP hxSw
                obtain ⟨f, hfF, hfx⟩ := hFalse x hxK hxP hxSw
                by_cases hfu : f = u
                · subst hfu
                  have h1 := hab_eval x
                  simp only [ha_lt, hb_lt, ↓reduceIte, hfx] at h1
                  have h2 : wireAt gates n x a = false ∨ wireAt gates n x b = false := by
                    cases hwa : wireAt gates n x a
                    · exact Or.inl rfl
                    · cases hwb : wireAt gates n x b
                      · exact Or.inr rfl
                      · simp [hwa, hwb] at h1
                  rcases h2 with hwa | hwb
                  · exact ⟨a, Finset.mem_insert_self a _, hwa⟩
                  · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self b _), hwb⟩
                · exact ⟨f, Finset.mem_insert_of_mem
                    (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hfu, hfF⟩)), hfx⟩
              · exact Finset.insert_subset_iff.mpr ⟨hj_spec, hAsub⟩
              · have h1 : (insert a (insert b (F.erase u))).card ≤ (insert b (F.erase u)).card + 1 :=
                  Finset.card_insert_le _ _
                have h2 : (insert b (F.erase u)).card ≤ (F.erase u).card + 1 :=
                  Finset.card_insert_le _ _
                have h3 : (F.erase u).card + 1 = F.card := Finset.card_erase_add_one huF
                have h4 : (insert j A).card = A.card + 1 := Finset.card_insert_of_notMem hj_not_A
                omega
              · intro y hy k hk
                rw [Finset.mem_insert] at hk
                have hyu : y < u := by
                  simp only [Finset.mem_insert] at hy
                  rcases hy with rfl | rfl | hy
                  · exact ha_lt
                  · exact hb_lt
                  · exact hErLt y hy
                rcases hk with rfl | hkA
                · omega
                · exact lt_trans hyu (hOrder u huF k hkA)
            · have hlen := hg.2
              rw [hinputs] at hlen
              simp at hlen
          · rcases hinputs : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · exfalso
              have h1 := hgate_eval (ind (S w))
              rw [hu_true, hop, hinputs] at h1
              simp [GateOp.eval] at h1
            · have ha_eval : ∀ x : Fin n → Bool,
                  wireAt gates n x u = if a < u then wireAt gates n x a else false := by
                intro x
                rw [hgate_eval x, hop, hinputs]
                simp [GateOp.eval]
              have ha_lt : a < u := by
                have h1 := ha_eval (ind (S w))
                rw [hu_true] at h1
                by_contra hno
                simp only [hno, ↓reduceIte] at h1
                exact Bool.false_ne_true h1.symm
              have ha_true : wireAt gates n (ind (S w)) a = true := by
                have h1 := ha_eval (ind (S w))
                simp only [hu_true, ha_lt, ↓reduceIte] at h1
                exact h1.symm
              refine ih u huB (insert a (F.erase u)) P A d
                ⟨?_, ?_, ?_, hAsub, ?_, ?_, hHit, hSize⟩
              · intro y hy
                rw [Finset.mem_insert] at hy
                rcases hy with rfl | hy
                · exact ha_lt
                · exact hErLt y hy
              · intro y hy
                rw [Finset.mem_insert] at hy
                rcases hy with rfl | hy
                · exact ha_true
                · exact hTrue y (Finset.erase_subset u F hy)
              · intro x hxK hxP hxSw
                obtain ⟨f, hfF, hfx⟩ := hFalse x hxK hxP hxSw
                by_cases hfu : f = u
                · subst hfu
                  refine ⟨a, Finset.mem_insert_self a _, ?_⟩
                  have h1 := ha_eval x
                  simp only [ha_lt, ↓reduceIte] at h1
                  rw [← h1, hfx]
                · exact ⟨f, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hfu, hfF⟩), hfx⟩
              · have h1 : (insert a (F.erase u)).card ≤ (F.erase u).card + 1 :=
                  Finset.card_insert_le a (F.erase u)
                have h2 : (F.erase u).card + 1 = F.card := Finset.card_erase_add_one huF
                omega
              · intro y hy k hk
                rw [Finset.mem_insert] at hy
                rcases hy with rfl | hy
                · exact lt_trans ha_lt (hOrder u huF k hk)
                · exact hOrder y (Finset.erase_subset u F hy) k hk
            · have hab_eval : ∀ x : Fin n → Bool,
                  wireAt gates n x u =
                    ((if a < u then wireAt gates n x a else false) ||
                      (if b < u then wireAt gates n x b else false)) := by
                intro x
                rw [hgate_eval x, hop, hinputs]
                simp [GateOp.eval]
              have hab_w := hab_eval (ind (S w))
              rw [hu_true] at hab_w
              have hbranch : (if a < u then wireAt gates n (ind (S w)) a else false) = true ∨
                  (if b < u then wireAt gates n (ind (S w)) b else false) = true := by
                cases h1 : (if a < u then wireAt gates n (ind (S w)) a else false) <;>
                  cases h2 : (if b < u then wireAt gates n (ind (S w)) b else false) <;>
                  simp [h1, h2] at hab_w ⊢
              rcases hbranch with ha_branch | hb_branch
              · have ha_lt : a < u := by
                  by_contra hno
                  simp only [hno, ↓reduceIte] at ha_branch
                  exact Bool.false_ne_true ha_branch
                have ha_true : wireAt gates n (ind (S w)) a = true := by
                  simp only [ha_lt, ↓reduceIte] at ha_branch
                  exact ha_branch
                refine ih u huB (insert a (F.erase u)) P A d
                  ⟨?_, ?_, ?_, hAsub, ?_, ?_, hHit, hSize⟩
                · intro y hy
                  rw [Finset.mem_insert] at hy
                  rcases hy with rfl | hy
                  · exact ha_lt
                  · exact hErLt y hy
                · intro y hy
                  rw [Finset.mem_insert] at hy
                  rcases hy with rfl | hy
                  · exact ha_true
                  · exact hTrue y (Finset.erase_subset u F hy)
                · intro x hxK hxP hxSw
                  obtain ⟨f, hfF, hfx⟩ := hFalse x hxK hxP hxSw
                  by_cases hfu : f = u
                  · subst hfu
                    refine ⟨a, Finset.mem_insert_self a _, ?_⟩
                    have h1 := hab_eval x
                    simp only [ha_lt, ↓reduceIte, hfx] at h1
                    cases hwa : wireAt gates n x a
                    · rfl
                    · simp [hwa] at h1
                  · exact ⟨f, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hfu, hfF⟩), hfx⟩
                · have h1 : (insert a (F.erase u)).card ≤ (F.erase u).card + 1 :=
                    Finset.card_insert_le a (F.erase u)
                  have h2 : (F.erase u).card + 1 = F.card := Finset.card_erase_add_one huF
                  omega
                · intro y hy k hk
                  rw [Finset.mem_insert] at hy
                  rcases hy with rfl | hy
                  · exact lt_trans ha_lt (hOrder u huF k hk)
                  · exact hOrder y (Finset.erase_subset u F hy) k hk
              · have hb_lt : b < u := by
                  by_contra hno
                  simp only [hno, ↓reduceIte] at hb_branch
                  exact Bool.false_ne_true hb_branch
                have hb_true : wireAt gates n (ind (S w)) b = true := by
                  simp only [hb_lt, ↓reduceIte] at hb_branch
                  exact hb_branch
                refine ih u huB (insert b (F.erase u)) P A d
                  ⟨?_, ?_, ?_, hAsub, ?_, ?_, hHit, hSize⟩
                · intro y hy
                  rw [Finset.mem_insert] at hy
                  rcases hy with rfl | hy
                  · exact hb_lt
                  · exact hErLt y hy
                · intro y hy
                  rw [Finset.mem_insert] at hy
                  rcases hy with rfl | hy
                  · exact hb_true
                  · exact hTrue y (Finset.erase_subset u F hy)
                · intro x hxK hxP hxSw
                  obtain ⟨f, hfF, hfx⟩ := hFalse x hxK hxP hxSw
                  by_cases hfu : f = u
                  · subst hfu
                    refine ⟨b, Finset.mem_insert_self b _, ?_⟩
                    have h1 := hab_eval x
                    simp only [hb_lt, ↓reduceIte, hfx] at h1
                    cases hwb : wireAt gates n x b
                    · rfl
                    · simp [hwb] at h1
                  · exact ⟨f, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hfu, hfF⟩), hfx⟩
                · have h1 : (insert b (F.erase u)).card ≤ (F.erase u).card + 1 :=
                    Finset.card_insert_le b (F.erase u)
                  have h2 : (F.erase u).card + 1 = F.card := Finset.card_erase_add_one huF
                  omega
                · intro y hy k hk
                  rw [Finset.mem_insert] at hy
                  rcases hy with rfl | hy
                  · exact lt_trans hb_lt (hOrder u huF k hk)
                  · exact hOrder y (Finset.erase_subset u F hy) k hk
            · have hlen := hg.2
              rw [hinputs] at hlen
              simp at hlen
        · push Not at hspec_j
          obtain ⟨v, hvw, hv_true_neq⟩ := hspec_j
          have hv_true : wireAt gates n (ind (S v)) u = true := by
            cases hval : wireAt gates n (ind (S v)) u
            · exact False.elim (hv_true_neq hval)
            · rfl
          refine ih u huB (F.erase u) (P ∪ S v) A (d + 1)
            ⟨hErLt, ?_, ?_, hAsub, ?_, ?_, ?_, ?_⟩
          · intro y hy
            exact hTrue y (Finset.erase_subset u F hy)
          · intro x hxK hxP hxSw
            have hxP' : ∀ p ∈ P, x p = true :=
              fun p hp => hxP p (Finset.mem_union_left (S v) hp)
            obtain ⟨f, hfF, hfx⟩ := hFalse x hxK hxP' hxSw
            refine ⟨f, Finset.mem_erase.mpr ⟨?_, hfF⟩, hfx⟩
            intro hfu
            have hmono : wireAt gates n x u = true := by
              refine wireAt_mono gates hgs_op n (ind (S v)) x ?_ u hv_true
              intro p hp
              simp only [ind, decide_eq_true_eq] at hp
              exact hxP p (Finset.mem_union_right P hp)
            rw [hfu, hmono] at hfx
            exact Bool.false_ne_true hfx.symm
          · have h1 : (F.erase u).card + 1 = F.card := Finset.card_erase_add_one huF
            omega
          · intro y hy k hk
            exact hOrder y (Finset.erase_subset u F hy) k hk
          · have hinter_eq : (P ∪ S v) ∩ S w = (P ∩ S w) ∪ (S v ∩ S w) :=
              Finset.union_inter_distrib_right P (S v) (S w)
            rw [hinter_eq]
            have h1 := Finset.card_union_le (P ∩ S w) (S v ∩ S w)
            have h2 := hinter v w hvw
            omega
          · right
            refine ⟨?_, v, Finset.subset_union_right⟩
            rcases hSize with hPd | ⟨hPdq, v₀, hv₀⟩
            · have h1 := Finset.card_union_le P (S v)
              have hSv := hcardS v
              have hdq : d ≤ d * q := Nat.le_mul_of_pos_right d (by omega)
              have hmul : (d + 1) * q + 1 = d * q + q + 1 := by ring
              omega
            · have hle_inter : 1 ≤ (P ∩ S v).card := by
                have hsub : S v ∩ S v₀ ⊆ P ∩ S v := by
                  intro z hz
                  rw [Finset.mem_inter] at hz ⊢
                  exact ⟨hv₀ hz.2, hz.1⟩
                have hcard_ge : 1 ≤ (S v ∩ S v₀).card := by
                  by_cases hvv₀ : v = v₀
                  · subst hvv₀
                    rw [Finset.inter_self, hcardS v]
                    omega
                  · rw [hinter v v₀ hvv₀]
                exact le_trans hcard_ge (Finset.card_le_card hsub)
              have hunion := Finset.card_union_add_card_inter P (S v)
              have hSv := hcardS v
              have hmul : (d + 1) * q + 1 = d * q + q + 1 := by ring
              omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hF
      subst hF
      have h0 : GoodState n K q S gates w 0 ∅ P A d := by
        refine ⟨?_, hgs.2.1, hgs.2.2.1, hgs.2.2.2.1, hgs.2.2.2.2.1, hgs.2.2.2.2.2.1,
          hgs.2.2.2.2.2.2.1, hgs.2.2.2.2.2.2.2⟩
        intro u hu
        simp at hu
      exact empty_contradiction q n m K S hq hcardS gates w c hcq hcK hspec P A d h0

lemma main :
    ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)),
      2 ≤ q →
      (∀ i : Fin m, (S i).card = q + 1) →
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
      ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
        (∀ g ∈ gates,
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ (w : Fin m) (x : Fin n → Bool),
          (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
            decide (∀ v ∈ S w, x v = true)) →
        ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  intro q n m K S hq hcardS hinter gates out hgates heval c hcq hcK
  by_cases hc0 : c = 0
  · subst hc0
    simp
  have hcpos : 1 ≤ c := Nat.pos_of_ne_zero hc0
  have hspec_ge : ∀ w : Fin m, c ≤ (spec gates S w).card := by
    intro w
    by_contra hlt
    have hspec : (spec gates S w).card < c := Nat.lt_of_not_le hlt
    refine descent_contradiction q n m K S hq hcardS hinter gates hgates w c hcq hcK hspec
      (out w + 1) {out w} ∅ ∅ 0 ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rw [Finset.mem_singleton] at hu
      omega
    · intro u hu
      rw [Finset.mem_singleton] at hu
      subst hu
      rw [← wireAt_eq_eval]
      have hwK : (Finset.univ.filter (fun i : Fin n => ind (S w) i = true)).card ≤ K := by
        rw [weight_ind, hcardS w]
        have h1 : 1 * q ≤ c * q := Nat.mul_le_mul_right q hcpos
        omega
      rw [heval w (ind (S w)) hwK]
      simp [ind]
    · intro x hxK hxP hxSw
      refine ⟨out w, Finset.mem_singleton_self _, ?_⟩
      rw [← wireAt_eq_eval, heval w x hxK]
      obtain ⟨v, hv, hxv⟩ := hxSw
      simp only [decide_eq_false_iff_not, not_forall]
      exact ⟨v, hv, by simp [hxv]⟩
    · exact Finset.empty_subset _
    · simp
    · intro u hu j hj
      simp at hj
    · simp
    · left
      simp
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) (spec gates S) := by
    intro w₁ _ w₂ _ hw
    exact spec_disjoint gates S hw
  have hsum : (∑ w : Fin m, (spec gates S w).card) ≤ gates.length := by
    rw [← Finset.card_biUnion hdisj]
    calc ((Finset.univ : Finset (Fin m)).biUnion (spec gates S)).card
        ≤ (Finset.univ : Finset (Fin gates.length)).card := Finset.card_le_univ _
      _ = gates.length := Finset.card_fin gates.length
  calc m * c = ∑ _w : Fin m, c := by simp [Finset.sum_const]
    _ ≤ ∑ w : Fin m, (spec gates S w).card := Finset.sum_le_sum fun w _ => hspec_ge w
    _ ≤ gates.length := hsum

end PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length :=
  PEqualNP.Outside.L_meta_925.main
