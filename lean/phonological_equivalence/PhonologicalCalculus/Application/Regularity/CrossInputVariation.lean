                  
                   
import PhonologicalCalculus.Application.Regularity.LatticeScore
import Mathlib.Data.List.Forall2
import Mathlib.Data.Set.Finite.List

namespace CrossInputVariation
open ShiftRegister
variable {Z D S O : Type}

def ecost (charge : Register Z → Option Z → ℝ) (del : D → ℝ) :
    Register Z → List (Sum D (Option Z)) → ℝ
  | _, [] => 0
  | q, Sum.inl d :: xs => del d + ecost charge del q xs
  | q, Sum.inr z :: xs => charge q z + ecost charge del (shift q z) xs

theorem ecost_append (f : Register Z → Option Z → ℝ) (del : D → ℝ)
    (q : Register Z) (xs ys : List (Sum D (Option Z))) :
    ecost f del q (xs ++ ys) = ecost f del q xs +
      ecost f del (xs.foldl eventStep q) ys := by
  induction xs generalizing q with
  | nil => simp [ecost]
  | cons a xs ih => cases a <;> simp [ecost,eventStep,ih,add_assoc]

theorem ecost_nonneg (f : Register Z → Option Z → ℝ) (del : D → ℝ)
    (hf : ∀ q z, 0 ≤ f q z) (hd : ∀ d, 0 ≤ del d)
    (q : Register Z) (xs : List (Sum D (Option Z))) : 0 ≤ ecost f del q xs := by
  induction xs generalizing q with
  | nil => simp [ecost]
  | cons a xs ih => cases a <;> simp only [ecost] <;> exact add_nonneg (by first | apply hf | apply hd) (ih _)

theorem ecost_bound (f : Register Z → Option Z → ℝ) (del : D → ℝ)
    (C : ℝ) (hf : ∀ q z, f q z ≤ C) (hd : ∀ d, del d ≤ C)
    (q : Register Z) (xs : List (Sum D (Option Z))) :
    ecost f del q xs ≤ xs.length * C := by
  induction xs generalizing q with
  | nil => simp [ecost]
  | cons a xs ih =>
    cases a with
    | inl d =>
      simp only [ecost,List.length_cons,Nat.cast_add,Nat.cast_one]
      have := hd d; have := ih q; nlinarith
    | inr z =>
      simp only [ecost,List.length_cons,Nat.cast_add,Nat.cast_one]
      have := hf q z; have := ih (shift q z); nlinarith

def charge (f : Z → Option Z → Option Z → Option Z → Option Z → ℝ)
    (q : Register Z) (z : Option Z) : ℝ :=
  match q 2 with | none => 0 | some c => f c (q 0) (q 1) (q 3) z

theorem delayed_objective
    (f : Z → Option Z → Option Z → Option Z → Option Z → ℝ)
    (del : D → ℝ) (xs : List (Option Z)) (a b c d : Option Z) :
    ecost (charge f) del (LocalScore.register a b c d)
      ((xs ++ [none,none]).map Sum.inr) = LatticeScore.objective f a b (c :: d :: xs) := by
  induction xs generalizing a b c d with
  | nil =>
    cases c <;> cases d <;>
      simp [ecost,charge,LocalScore.register,shift,LatticeScore.objective] <;> rfl
  | cons z xs ih =>
    simp only [List.cons_append,List.map_cons,ecost,LocalScore.shift_register]
    rw [ih]
    rfl

theorem stream_objective
    (f : Z → Option Z → Option Z → Option Z → Option Z → ℝ)
    (del : D → ℝ) (xs : List (Option Z)) :
    ecost (charge f) del (fun _ => none)
      ((xs ++ [none,none]).map Sum.inr) = LatticeScore.objective f none none xs := by
  have h := delayed_objective f del xs none none none none
  have eq : LocalScore.register (Z := Z) none none none none = (fun _ => none) := by
    funext i; rcases i with ⟨i,hi⟩; interval_cases i <;> rfl
  rw [eq] at h
  simpa [LatticeScore.objective] using h

theorem delete_split
    (f : Z → Option Z → Option Z → Option Z → Option Z → ℝ)
    (del : D → ℝ) (q : Register Z) (xs : List (Sum D Z)) :
    ecost (charge f) del q (events xs ++ [Sum.inr none,Sum.inr none]) =
      LatticeScore.deleteCost del xs + ecost (charge f) del q
        (((LocalScore.survivors xs).map some ++ [none,none]).map Sum.inr) := by
  induction xs generalizing q with
  | nil => simp [events,LatticeScore.deleteCost,LocalScore.survivors]
  | cons a xs ih =>
    cases a with
    | inl d =>
      change del d + ecost (charge f) del q (events xs ++ [Sum.inr none,Sum.inr none]) = _
      rw [ih]
      simp [LatticeScore.deleteCost,LocalScore.survivors,add_assoc]
    | inr z =>
      change charge f q (some z) + ecost (charge f) del (shift q (some z))
          (events xs ++ [Sum.inr none,Sum.inr none]) = _
      rw [ih]
      simp [LatticeScore.deleteCost,LocalScore.survivors,ecost,add_left_comm]

theorem native_score_bridge
    (f : (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → ℝ)
    (del : ReferenceWindows.Window S → ℝ) (xs : List (RegularProjection.Token S O)) :
    ecost (charge f) del (fun _ => none) (events xs ++ [Sum.inr none,Sum.inr none]) =
      LatticeScore.nativeScore f del xs := by
  rw [delete_split,stream_objective]
  rfl

theorem annotation_prefix (p x y : List S) (a b : Option S) :
    (ReferenceWindows.annotate a b (p++x)).take (p.length-2) =
    (ReferenceWindows.annotate a b (p++y)).take (p.length-2) := by
  induction p generalizing a b with
  | nil => simp
  | cons c p ih =>
    cases p with
    | nil => simp
    | cons d p =>
      cases p with
      | nil => simp
      | cons e p =>
        simpa [ReferenceWindows.annotate,List.length_cons,Nat.add_sub_cancel,
          List.take_succ_cons] using congrArg (List.cons ⟨a,b,c,some d,some e⟩)
          (ih b (some c))

def token (w : ReferenceWindows.Window S) : Option O → RegularProjection.Token S O
  | none => Sum.inl w
  | some o => Sum.inr (w,o)

def tokens (us : List S) (os : List (Option O)) : List (RegularProjection.Token S O) :=
  List.zipWith token (ReferenceWindows.annotate none none us) os

theorem annotate_length (us : List S) (a b : Option S) :
    (ReferenceWindows.annotate a b us).length = us.length := by
  simpa only [List.length_map] using congrArg List.length (ReferenceWindows.annotate_centers us a b)

theorem tokens_length (us : List S) (os : List (Option O)) (h : us.length = os.length) :
    (tokens us os).length = us.length := by simp [tokens,annotate_length,h]

theorem token_input (w : ReferenceWindows.Window S) (o : Option O) :
    RegularProjection.input (token w o) = w := by cases o <;> rfl

theorem token_output (w : ReferenceWindows.Window S) (o : Option O) :
    RegularProjection.output (token w o) = o := by cases o <;> rfl

theorem zipped_input (ws : List (ReferenceWindows.Window S)) (os : List (Option O))
    (h : ws.length = os.length) :
    (List.zipWith token ws os).map RegularProjection.input = ws := by
  induction ws generalizing os with
  | nil => simp
  | cons w ws ih =>
    cases os with
    | nil => simp at h
    | cons o os =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at h
      simpa [token_input] using congrArg (List.cons w) (ih os h)

theorem tokens_input (us : List S) (os : List (Option O)) (h : us.length = os.length) :
    (tokens us os).map RegularProjection.input = ReferenceWindows.annotate none none us :=
  zipped_input _ _ (by simpa [annotate_length] using h)

theorem choices_splice (ok : S → Option O → Prop) (p x y : List S)
    (ox oy : List (Option O)) (hx : List.Forall₂ ok (p++x) ox)
    (hy : List.Forall₂ ok (p++y) oy) (n : ℕ) (hn : n ≤ p.length) :
    List.Forall₂ ok (p++y) (ox.take n ++ oy.drop n) := by
  have ht := List.forall₂_take n hx
  have hd := List.forall₂_drop n hy
  rw [List.take_append_of_le_length hn] at ht
  have ht' : List.Forall₂ ok ((p++y).take n) (ox.take n) := by
    simpa only [List.take_append_of_le_length hn] using ht
  simpa using List.rel_append ht' hd

theorem tokens_prefix (p x y : List S) (ox oy : List (Option O))
    (hox : (p++x).length = ox.length) :
    (tokens (p++x) ox).take (p.length-2) =
      (tokens (p++y) (ox.take (p.length-2) ++ oy.drop (p.length-2))).take (p.length-2) := by
  have ht : (ox.take (p.length-2)).length = p.length-2 := by
    rw [List.length_take]; apply Nat.min_eq_left
    simp only [List.length_append] at hox
    omega
  simp only [tokens,List.take_zipWith]
  rw [annotation_prefix p x y none none]
  congr 1
  have hh := List.take_append_length (l₁ := ox.take (p.length-2)) (l₂ := oy.drop (p.length-2))
  rw [ht] at hh
  exact hh.symm

theorem event_prefix_bound (f : Register Z → Option Z → ℝ) (del : D → ℝ)
    (C : ℝ) (hf0 : ∀ q z, 0 ≤ f q z) (hd0 : ∀ d, 0 ≤ del d)
    (hf : ∀ q z, f q z ≤ C) (hd : ∀ d, del d ≤ C)
    (xs ys : List (Sum D Z)) (n : ℕ) (he : xs.take n = ys.take n) :
    ecost f del (fun _ => none) (events ys ++ [Sum.inr none,Sum.inr none]) ≤
      ecost f del (fun _ => none) (events xs ++ [Sum.inr none,Sum.inr none]) +
        ((ys.drop n).length + 2 : ℕ) * C := by
  have split (zs : List (Sum D Z)) :
      events zs ++ [Sum.inr none,Sum.inr none] =
        events (zs.take n) ++ (events (zs.drop n) ++ [Sum.inr none,Sum.inr none]) := by
    simp only [events,← List.append_assoc,← List.map_append,List.take_append_drop]
  have decomp (zs : List (Sum D Z)) :
      ecost f del (fun _ => none) (events zs ++ [Sum.inr none,Sum.inr none]) =
        ecost f del (fun _ => none) (events (zs.take n)) +
        ecost f del ((events (zs.take n)).foldl eventStep (fun _ => none))
          (events (zs.drop n) ++ [Sum.inr none,Sum.inr none]) := by
    rw [split zs]; exact ecost_append f del _ _ _
  rw [decomp xs,decomp ys,← he]
  have hn := ecost_nonneg f del hf0 hd0
    ((events (xs.take n)).foldl eventStep (fun _ => none))
    (events (xs.drop n) ++ [Sum.inr none,Sum.inr none])
  have hb := ecost_bound f del C hf hd
    ((events (xs.take n)).foldl eventStep (fun _ => none))
    (events (ys.drop n) ++ [Sum.inr none,Sum.inr none])
  change ecost f del ((events (xs.take n)).foldl eventStep (fun _ => none))
      (events (ys.drop n) ++ [Sum.inr none,Sum.inr none]) ≤ _ at hb
  simp only [List.length_append,events,List.length_map,List.length_cons,List.length_nil] at hb
  change _ ≤ ((ys.drop n).length+2 : ℕ)*C at hb
  dsimp only [events] at hn ⊢
  linarith

abbrev Scorer (S O : Type) :=
  (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
  Option (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
  Option (ReferenceWindows.Window S × O) → ℝ

def score (f : Scorer S O) (del : ReferenceWindows.Window S → ℝ)
    (us : List S) (os : List (Option O)) : ℝ :=
  LatticeScore.nativeScore f del (tokens us os)

theorem charge_bounds (f : Scorer S O) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z a b c d, 0 ≤ f z a b c d ∧ f z a b c d ≤ C) :
    (∀ q z, 0 ≤ charge f q z) ∧ (∀ q z, charge f q z ≤ C) := by
  constructor <;> intro q z <;> unfold charge <;> cases q 2 with
  | none => simpa using hC
  | some c => first | exact (hf c _ _ _ _).1 | exact (hf c _ _ _ _).2

theorem score_splice (f : Scorer S O) (del : ReferenceWindows.Window S → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z a b c d, 0 ≤ f z a b c d ∧ f z a b c d ≤ C)
    (hd : ∀ d, 0 ≤ del d ∧ del d ≤ C)
    (ok : S → Option O → Prop) (p x y : List S) (ox oy : List (Option O))
    (hx : List.Forall₂ ok (p++x) ox) (hy : List.Forall₂ ok (p++y) oy) :
    score f del (p++y) (ox.take (p.length-2) ++ oy.drop (p.length-2)) ≤
      score f del (p++x) ox + (4 + y.length : ℕ)*C := by
  have ha := choices_splice ok p x y ox oy hx hy (p.length-2) (by omega)
  have hb := charge_bounds f C hC hf
  have he := tokens_prefix p x y ox oy hx.length_eq
  have bound := event_prefix_bound (charge f) del C hb.1 (fun d => (hd d).1)
    hb.2 (fun d => (hd d).2) _ _ (p.length-2) he
  rw [native_score_bridge,native_score_bridge] at bound
  have hl := tokens_length (p++y) _ ha.length_eq
  have hn : ((tokens (p++y) (ox.take (p.length-2) ++ oy.drop (p.length-2))).drop
      (p.length-2)).length + 2 ≤ 4 + y.length := by
    rw [List.length_drop,hl,List.length_append]; omega
  have hm : (((tokens (p++y) (ox.take (p.length-2) ++ oy.drop (p.length-2))).drop
      (p.length-2)).length + 2 : ℕ)*C ≤ (4+y.length : ℕ)*C :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hC
  exact bound.trans (by dsimp [score]; linarith)

def winner (f : Scorer S O) (del : ReferenceWindows.Window S → ℝ)
    (ok : S → Option O → Prop) (us : List S) (os : List (Option O)) : Prop :=
  List.Forall₂ ok us os ∧ ∀ ps, List.Forall₂ ok us ps → score f del us os ≤ score f del us ps

theorem cross_input_one_sided (f : Scorer S O) (del : ReferenceWindows.Window S → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z a b c d, 0 ≤ f z a b c d ∧ f z a b c d ≤ C)
    (hd : ∀ d, 0 ≤ del d ∧ del d ≤ C)
    (ok : S → Option O → Prop) (p x y : List S) (ox oy : List (Option O))
    (hx : winner f del ok (p++x) ox) (hy : winner f del ok (p++y) oy) :
    score f del (p++y) oy ≤ score f del (p++x) ox + (4+y.length : ℕ)*C := by
  apply le_trans (hy.2 _ (choices_splice ok p x y ox oy hx.1 hy.1 (p.length-2) (by omega)))
  exact score_splice f del C hC hf hd ok p x y ox oy hx.1 hy.1

theorem cross_input_bound (f : Scorer S O) (del : ReferenceWindows.Window S → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z a b c d, 0 ≤ f z a b c d ∧ f z a b c d ≤ C)
    (hd : ∀ d, 0 ≤ del d ∧ del d ≤ C)
    (ok : S → Option O → Prop) (p x y : List S) (ox oy : List (Option O))
    (hx : winner f del ok (p++x) ox) (hy : winner f del ok (p++y) oy) :
    |score f del (p++x) ox - score f del (p++y) oy| ≤ 4*C + C*(x.length+y.length) := by
  have hxy := cross_input_one_sided f del C hC hf hd ok p x y ox oy hx hy
  have hyx := cross_input_one_sided f del C hC hf hd ok p y x oy ox hy hx
  simp only [Nat.cast_add,Nat.cast_ofNat] at hxy hyx
  have hx0 : (0:ℝ) ≤ x.length := Nat.cast_nonneg _
  have hy0 : (0:ℝ) ≤ y.length := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> nlinarith

theorem winner_exists [Finite O] (f : Scorer S O) (del : ReferenceWindows.Window S → ℝ)
    (ok : S → Option O → Prop) (us : List S)
    (hne : ∃ os, List.Forall₂ ok us os) : ∃ os, winner f del ok us os := by
  have hfin : {os : List (Option O) | List.Forall₂ ok us os}.Finite := by
    apply (List.finite_length_eq (Option O) us.length).subset
    intro os hos
    exact hos.length_eq.symm
  exact Set.exists_min_image _ (score f del us) hfin hne

theorem zipped_allowed (ok : S → Option O → Prop)
    (ws : List (ReferenceWindows.Window S)) (os : List (Option O))
    (h : List.Forall₂ ok (ws.map ReferenceWindows.Window.c) os) :
    ∀ t ∈ List.zipWith token ws os, ok (RegularProjection.input t).c (RegularProjection.output t) := by
  induction ws generalizing os with
  | nil => simp
  | cons w ws ih =>
    cases os with
    | nil => simp at h
    | cons o os =>
      simp only [List.map_cons,List.forall₂_cons] at h
      intro t ht
      simp only [List.zipWith_cons_cons,List.mem_cons] at ht
      rcases ht with rfl | ht
      · simpa only [token_input,token_output] using h.1
      · exact ih os h.2 t ht

theorem tokens_admissible (ok : S → Option O → Prop) (us : List S) (os : List (Option O))
    (h : List.Forall₂ ok us os) :
    ReferenceWindows.valid ((tokens us os).map RegularProjection.input) ∧
    (∀ t ∈ tokens us os, ok (RegularProjection.input t).c (RegularProjection.output t)) ∧
    (tokens us os).map (fun t => (RegularProjection.input t).c) = us := by
  have hi := tokens_input us os h.length_eq
  refine ⟨?_,?_,?_⟩
  · rw [hi]; exact ReferenceWindows.annotate_valid us
  · apply zipped_allowed
    simpa only [ReferenceWindows.annotate_centers] using h
  · have hh := congrArg (List.map ReferenceWindows.Window.c) hi
    simpa only [List.map_map,Function.comp_def,ReferenceWindows.annotate_centers] using hh

theorem choices_of_native (ok : S → Option O → Prop) (xs : List (RegularProjection.Token S O))
    (h : ∀ t ∈ xs, ok (RegularProjection.input t).c (RegularProjection.output t)) :
    List.Forall₂ ok (xs.map (fun t => (RegularProjection.input t).c))
      (xs.map RegularProjection.output) := by
  induction xs with
  | nil => exact .nil
  | cons t xs ih => exact .cons (h t (by simp)) (ih (by intro s hs; exact h s (by simp [hs])))

theorem tokens_reconstruct (xs : List (RegularProjection.Token S O))
    (h : ReferenceWindows.valid (xs.map RegularProjection.input)) :
    tokens (xs.map (fun t => (RegularProjection.input t).c)) (xs.map RegularProjection.output) = xs := by
  have ha := (ReferenceWindows.valid_iff_canonical _).mp h
  have hz : List.zipWith token (xs.map RegularProjection.input) (xs.map RegularProjection.output) = xs := by
    clear h ha
    induction xs with
    | nil => rfl
    | cons t xs ih =>
      cases t with
      | inl w => simpa [token,RegularProjection.input,RegularProjection.output] using congrArg (List.cons (Sum.inl w)) ih
      | inr z => simpa [token,RegularProjection.input,RegularProjection.output] using congrArg (List.cons (Sum.inr z)) ih
  unfold tokens
  rw [show ReferenceWindows.annotate none none (xs.map (fun t => (RegularProjection.input t).c)) =
      xs.map RegularProjection.input by simpa only [List.map_map,Function.comp_def] using ha.symm]
  exact hz

theorem native_winner_of_choices (f : Scorer S O) (del : ReferenceWindows.Window S → ℝ)
    (ok : S → Option O → Prop) (us : List S) (os : List (Option O))
    (h : winner f del ok us os) : LatticeScore.nativeWinner f del ok (tokens us os) := by
  obtain ⟨hv,ha,hu⟩ := tokens_admissible ok us os h.1
  refine ⟨hv,ha,?_⟩
  intro ys hyv hya he
  have hyc := choices_of_native ok ys hya
  rw [he,hu] at hyc
  have hs := h.2 _ hyc
  have hyr := tokens_reconstruct ys hyv
  rw [he,hu] at hyr
  simpa only [score,hyr] using hs

theorem native_winner_exists [Finite O] (f : Scorer S O) (del : ReferenceWindows.Window S → ℝ)
    (ok : S → Option O → Prop) (us : List S)
    (hne : ∃ xs : List (RegularProjection.Token S O),
      ReferenceWindows.valid (xs.map RegularProjection.input) ∧
      (∀ t ∈ xs, ok (RegularProjection.input t).c (RegularProjection.output t)) ∧
      xs.map (fun t => (RegularProjection.input t).c) = us) :
    ∃ xs, LatticeScore.nativeWinner f del ok xs ∧
      xs.map (fun t => (RegularProjection.input t).c) = us := by
  obtain ⟨xs,hv,ha,hu⟩ := hne
  have hc := choices_of_native ok xs ha
  rw [hu] at hc
  obtain ⟨os,hos⟩ := winner_exists f del ok us ⟨_,hc⟩
  exact ⟨tokens us os,native_winner_of_choices f del ok us os hos,(tokens_admissible ok us os hos.1).2.2⟩

theorem choices_winner_of_native (f : Scorer S O) (del : ReferenceWindows.Window S → ℝ)
    (ok : S → Option O → Prop) (xs : List (RegularProjection.Token S O))
    (h : LatticeScore.nativeWinner f del ok xs) :
    winner f del ok (xs.map (fun t => (RegularProjection.input t).c)) (xs.map RegularProjection.output) := by
  refine ⟨choices_of_native ok xs h.2.1,?_⟩
  intro os hos
  obtain ⟨hv,ha,hu⟩ := tokens_admissible ok _ os hos
  have hw := h.2.2 _ hv ha hu
  simpa only [score,tokens_reconstruct xs h.1] using hw

theorem native_cross_input_bound (f : Scorer S O) (del : ReferenceWindows.Window S → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z a b c d, 0 ≤ f z a b c d ∧ f z a b c d ≤ C)
    (hd : ∀ d, 0 ≤ del d ∧ del d ≤ C)
    (ok : S → Option O → Prop) (p x y : List S)
    (xs ys : List (RegularProjection.Token S O))
    (hx : LatticeScore.nativeWinner f del ok xs) (hy : LatticeScore.nativeWinner f del ok ys)
    (hux : xs.map (fun t => (RegularProjection.input t).c) = p++x)
    (huy : ys.map (fun t => (RegularProjection.input t).c) = p++y) :
    |LatticeScore.nativeScore f del xs - LatticeScore.nativeScore f del ys| ≤
      4*C + C*(x.length+y.length) := by
  have hcx := choices_winner_of_native f del ok xs hx
  have hcy := choices_winner_of_native f del ok ys hy
  rw [hux] at hcx
  rw [huy] at hcy
  have hb := cross_input_bound f del C hC hf hd ok p x y _ _ hcx hcy
  rw [← hux,← huy] at hb
  simpa only [score,tokens_reconstruct xs hx.1,tokens_reconstruct ys hy.1] using hb

end CrossInputVariation
