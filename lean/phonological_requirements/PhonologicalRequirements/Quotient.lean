                                        
namespace PhonologicalRequirements
namespace Quotient

inductive Seg where
  | t | a | absent
deriving DecidableEq, Repr

def present : Seg → Bool
  | .absent => false
  | _ => true

def vocalic : Seg → Bool
  | .a => true
  | _ => false

def hiatus : List Seg → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: rest => (if vocalic x && vocalic y then 1 else 0) + hiatus (y :: rest)

def linear (r0 r1 : Seg) (c0 c1 c2 : List Seg) : List Seg :=
  (c0 ++ [r0] ++ c1 ++ [r1] ++ c2).filter present

def dep (cs : List Seg) : Nat := (cs.filter present).length

def score (r0 r1 : Seg) (c0 c1 c2 : List Seg) : Nat :=
  2 * (dep c0 + dep c1 + dep c2) + 10 * ((if present r0 then 0 else 1) + (if present r1 then 0 else 1))
    + 6 * hiatus (linear r0 r1 c0 c1 c2)

theorem dep_replicate_absent (k : Nat) : dep (List.replicate k Seg.absent) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [dep, List.replicate, List.filter, present] using ih

theorem filter_replicate_absent (k : Nat) : (List.replicate k Seg.absent).filter present = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate, List.filter, present] using ih

theorem score_absent_created (r0 r1 : Seg) (i j l : Nat) (h0 : present r0 = true) (h1 : present r1 = true) :
    score r0 r1 (List.replicate i .absent) (List.replicate j .absent) (List.replicate l .absent)
      = 6 * hiatus [r0, r1] := by
  simp [score, dep_replicate_absent, linear, List.filter_append, filter_replicate_absent, h0, h1, List.filter]

theorem score_zero_iff_pair (r0 r1 : Seg) (i j l : Nat) :
    score r0 r1 (List.replicate i .absent) (List.replicate j .absent) (List.replicate l .absent) = 0 ↔
      (r0 = .t ∧ r1 = .t) ∨ (r0 = .t ∧ r1 = .a) ∨ (r0 = .a ∧ r1 = .t) := by
  cases r0 <;> cases r1 <;> simp [score, dep_replicate_absent, linear, List.filter_append, filter_replicate_absent, present, hiatus, vocalic, List.filter]

theorem dep_pos_of_present (cs : List Seg) (x : Seg) (hx : x ∈ cs) (hp : present x = true) : 0 < dep cs := by
  unfold dep
  have : x ∈ cs.filter present := List.mem_filter.mpr ⟨hx, hp⟩
  exact List.length_pos_of_mem this

theorem score_pos_of_present_created (r0 r1 : Seg) (c0 c1 c2 : List Seg) (x : Seg) (hp : present x = true)
    (hx : x ∈ c0 ∨ x ∈ c1 ∨ x ∈ c2) : 0 < score r0 r1 c0 c1 c2 := by
  unfold score
  rcases hx with h | h | h
  · have := dep_pos_of_present c0 x h hp; omega
  · have := dep_pos_of_present c1 x h hp; omega
  · have := dep_pos_of_present c2 x h hp; omega

def placements : Nat → List (Nat × Nat × Nat)
  | 0 => [(0, 0, 0)]
  | k + 1 => (placements k).map (fun p => (p.1 + 1, p.2.1, p.2.2)) ++ (List.range (k + 2)).map (fun j => (0, j, k + 1 - j))

theorem placements_length : ∀ k, 2 * (placements k).length = (k + 1) * (k + 2)
  | 0 => rfl
  | k + 1 => by
    have ih := placements_length k
    simp only [placements, List.length_append, List.length_map, List.length_range]
    have : (k + 1 + 1) * (k + 1 + 2) = (k + 1) * (k + 2) + 2 * (k + 2) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    omega

theorem mem_placements : ∀ k i j l, (i, j, l) ∈ placements k ↔ i + j + l = k
  | 0, i, j, l => by
    simp only [placements, List.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; rfl
    · intro h; exact ⟨by omega, by omega, by omega⟩
  | k + 1, i, j, l => by
    simp only [placements, List.mem_append, List.mem_map, List.mem_range]
    constructor
    · rintro (⟨⟨i', j', l'⟩, hm, h⟩ | ⟨j', hj, h⟩)
      · have hm' := (mem_placements k i' j' l').mp hm
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3⟩ := h
        omega
      · simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3⟩ := h
        omega
    · intro h
      rcases Nat.eq_zero_or_pos i with hi | hi
      · right
        refine ⟨j, by omega, ?_⟩
        have hl : k + 1 - j = l := by omega
        rw [hl, hi]
      · left
        refine ⟨(i - 1, j, l), (mem_placements k (i - 1) j l).mpr (by omega), ?_⟩
        rw [Nat.sub_add_cancel hi]

theorem placements_nodup : ∀ k, (placements k).Nodup
  | 0 => by simp [placements]
  | k + 1 => by
    simp only [placements]
    refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
    · refine List.Pairwise.map _ ?_ (placements_nodup k)
      intro (p : Nat × Nat × Nat) (q : Nat × Nat × Nat) hpq h
      apply hpq
      rcases p with ⟨a, b, c⟩
      rcases q with ⟨d, e, f⟩
      simp only [Prod.mk.injEq] at h
      simp only [Prod.mk.injEq]
      omega
    · refine List.Pairwise.map _ ?_ List.nodup_range
      intro (a : Nat) (b : Nat) hab h
      apply hab
      simp only [Prod.mk.injEq] at h
      exact h.2.1
    · intro p hp q hq hpq
      rw [List.mem_map] at hp hq
      obtain ⟨⟨a, b, c⟩, _, rfl⟩ := hp
      obtain ⟨j, _, rfl⟩ := hq
      simp only [Prod.mk.injEq] at hpq
      omega

theorem score_zero_count (k : Nat) :
    2 * (3 * (placements k).length) = 3 * ((k + 1) * (k + 2)) := by
  have := placements_length k
  omega

theorem quotient_minimum (k : Nat) :
    score .t .a (List.replicate k .t) [] [] = 2 * k ∧
    (∀ (c0 c1 c2 : List Seg), c0.length + c1.length + c2.length = k →
      (∀ x, x ∈ c0 ∨ x ∈ c1 ∨ x ∈ c2 → present x = true) → 2 * k ≤ score .t .a c0 c1 c2) := by
  constructor
  · have hd : dep (List.replicate k Seg.t) = k := by
      induction k with
      | zero => rfl
      | succ k ih => simpa [dep, List.replicate, List.filter, present] using ih
    have hl : (List.replicate k Seg.t).filter present = List.replicate k Seg.t := by
      induction k with
      | zero => rfl
      | succ k ih => simpa [List.replicate, List.filter, present] using ih
    have hh : ∀ n, hiatus (List.replicate n Seg.t ++ [Seg.t, Seg.a]) = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        cases n with
        | zero => rfl
        | succ n => simpa [List.replicate, hiatus, vocalic] using ih
    have hde : dep [] = 0 := rfl
    simp [score, hd, hde, linear, List.filter_append, hl, present, List.filter, hh]
  · intro c0 c1 c2 hlen hpres
    have h0 : dep c0 = c0.length := by
      unfold dep
      rw [List.filter_eq_self.mpr (fun x hx => hpres x (Or.inl hx))]
    have h1 : dep c1 = c1.length := by
      unfold dep
      rw [List.filter_eq_self.mpr (fun x hx => hpres x (Or.inr (Or.inl hx)))]
    have h2 : dep c2 = c2.length := by
      unfold dep
      rw [List.filter_eq_self.mpr (fun x hx => hpres x (Or.inr (Or.inr hx)))]
    unfold score
    rw [h0, h1, h2]
    omega

end Quotient
end PhonologicalRequirements
