                   
import PhonologicalCalculus.Application.Regularity.BoundedMemory

namespace WeightedCost
open BoundedMemory
variable {Q A I : Type} (M : Machine Q A I) (K : ℕ)

abbrev Control (Q : Type) (K : ℕ) := Set (Q × Fin (K+1))

def expanded (V : Control Q K) (i : I) : Set (Q × ℕ) :=
  {p | ∃ q r, (q,r) ∈ V ∧ ∃ a, M.allowed a ∧ M.input a = i ∧
    p = (M.step q a,r.val + M.weight q a)}

noncomputable def emission (V : Control Q K) (i : I) : ℕ :=
  sInf (Prod.snd '' expanded M K V i)

def next (V : Control Q K) (i : I) : Control Q K :=
  {p | (p.1,emission M K V i + p.2.val) ∈ expanded M K V i}

def initial : Control Q K := {(M.start,0)}

noncomputable def run (us : List I) : ℕ × Control Q K :=
  us.foldl (fun s i => (s.1 + emission M K s.2 i,next M K s.2 i)) (0,initial M K)

theorem run_nil : run M K [] = (0,initial M K) := rfl

theorem run_append (us : List I) (i : I) : run M K (us ++ [i]) =
    ((run M K us).1 + emission M K (run M K us).2 i,next M K (run M K us).2 i) := by
  simp [run,List.foldl_append]

theorem emission_le {V : Control Q K} {i : I} {q : Q} {c : ℕ}
    (h : (q,c) ∈ expanded M K V i) : emission M K V i ≤ c :=
  Nat.sInf_le ⟨(q,c),h,rfl⟩

theorem emission_attained {V : Control Q K} {i : I}
    (h : (expanded M K V i).Nonempty) :
    ∃ q, (q,emission M K V i) ∈ expanded M K V i := by
  obtain ⟨⟨q,c⟩,hp,he⟩ := Nat.sInf_mem (h.image Prod.snd)
  exact ⟨q,by simpa [emission,← he] using hp⟩

def Sound (o : ℕ) (V : Control Q K) (us : List I) : Prop :=
  ∀ q r, (q,r) ∈ V → ∃ xs, M.valid xs ∧ xs.map M.input = us ∧
    M.state M.start xs = q ∧ M.cost M.start xs = o+r.val

theorem expanded_sound {o : ℕ} {V : Control Q K} {us : List I}
    (h : Sound M K o V us) {i : I} {q : Q} {c : ℕ}
    (he : (q,c) ∈ expanded M K V i) :
    ∃ xs, M.valid xs ∧ xs.map M.input = us ++ [i] ∧
      M.state M.start xs = q ∧ M.cost M.start xs = o+c := by
  rcases he with ⟨q₀,r,hr,a,ha,hi,eq⟩
  obtain ⟨xs,hv,hm,hs,hc⟩ := h q₀ r hr
  have hq : q = M.step q₀ a := congrArg Prod.fst eq
  have hec : c = r.val + M.weight q₀ a := congrArg Prod.snd eq
  refine ⟨xs ++ [a],(M.valid_append _ _).mpr ⟨hv,?_⟩,?_,?_,?_⟩
  · simpa [Machine.valid] using ha
  · simp [hm,hi]
  · rw [M.state_append,hs]
    exact hq.symm
  · simp [M.cost_append,Machine.cost,hs,hc,hec,Nat.add_assoc]

theorem next_sound {o : ℕ} {V : Control Q K} {us : List I}
    (h : Sound M K o V us) (i : I) :
    Sound M K (o+emission M K V i) (next M K V i) (us ++ [i]) := by
  intro q r hr
  obtain ⟨xs,hv,hm,hs,hc⟩ := expanded_sound M K h hr
  exact ⟨xs,hv,hm,hs,by simpa [Nat.add_assoc] using hc⟩

theorem run_sound (us : List I) : Sound M K (run M K us).1 (run M K us).2 us := by
  induction us using List.reverseRecOn with
  | nil =>
    intro q r hr
    have he : (q,r) = (M.start,(0 : Fin (K+1))) := hr
    cases he
    exact ⟨[],by simp [Machine.valid],rfl,rfl,rfl⟩
  | append_singleton us i ih =>
    rw [run_append]
    exact next_sound M K ih i

theorem optimal_prefix_retained (hb : M.bounded K) (xs : List A) :
    ∀ zs, M.winner (xs ++ zs) →
      ∃ r, (M.state M.start xs,r) ∈ (run M K (xs.map M.input)).2 ∧
        M.cost M.start xs = (run M K (xs.map M.input)).1 + r.val := by
  induction xs using List.reverseRecOn with
  | nil =>
    intros
    exact ⟨0,Set.mem_singleton _,rfl⟩
  | append_singleton xs a ih =>
    intro zs hw
    have hw' : M.winner (xs ++ (a :: zs)) := by simpa [List.append_assoc] using hw
    obtain ⟨r,hr,hc⟩ := ih _ hw'
    let s := run M K (xs.map M.input)
    let q := M.state M.start xs
    let c := r.val + M.weight q a
    let m := emission M K s.2 (M.input a)
    have ha : M.allowed a := hw.1 a (by simp)
    have he : (M.step q a,c) ∈ expanded M K s.2 (M.input a) :=
      ⟨q,r,hr,a,ha,rfl,rfl⟩
    have hmc : m ≤ c := emission_le M K he
    obtain ⟨q₀,hq₀⟩ := emission_attained M K ⟨_,he⟩
    obtain ⟨ys,hy,hym,hys,hyc⟩ := expanded_sound M K (run_sound M K _) hq₀
    have hbase : M.base (xs ++ [a]) ≤ s.1 + m := by
      have hs : M.same ys (xs ++ [a]) := by simpa [Machine.same] using hym
      have hh := M.base_le hy hs
      simpa [hyc,s,m] using hh
    have hbnd := M.optimal_prefix_bound K hb hw
    have hcost : M.cost M.start (xs ++ [a]) = s.1 + c := by
      simp [M.cost_append,Machine.cost,hc,s,c,q,Nat.add_assoc]
    have hcm : c ≤ m+K := by omega
    let rr : Fin (K+1) := ⟨c-m,by omega⟩
    refine ⟨rr,?_,?_⟩
    · simp only [List.map_append,List.map_singleton,run_append]
      change (M.state M.start (xs ++ [a]),m+rr.val) ∈ expanded M K s.2 (M.input a)
      have hs : M.state M.start (xs ++ [a]) = M.step q a := by
        simp [M.state_append,Machine.state,q]
      rw [hs]
      have heq : m+rr.val=c := by dsimp [rr]; omega
      rwa [heq]
    · simp only [List.map_append,List.map_singleton,run_append]
      change M.cost M.start (xs ++ [a]) = (s.1+m)+rr.val
      dsimp [rr]
      omega

theorem winner_exists {us : List I} (h : ∃ xs, M.valid xs ∧ xs.map M.input = us) :
    ∃ xs, M.winner xs ∧ xs.map M.input = us := by
  let S : Set ℕ := {n | ∃ xs, M.valid xs ∧ xs.map M.input = us ∧ M.total M.start xs = n}
  obtain ⟨xs,hv,hm⟩ := h
  have hn : S.Nonempty := ⟨M.total M.start xs,xs,hv,hm,rfl⟩
  obtain ⟨ys,hy,hym,hyc⟩ := Nat.sInf_mem hn
  refine ⟨ys,⟨hy,?_⟩,hym⟩
  intro zs hz hs
  rw [hyc]
  exact Nat.sInf_le ⟨zs,hz,hs.trans hym,rfl⟩

def finalCosts (V : Control Q K) : Set ℕ :=
  {n | ∃ q r, (q,r) ∈ V ∧ n = r.val + M.final q}

noncomputable def terminal (V : Control Q K) : Option ℕ := by
  classical
  exact if V.Nonempty then some (sInf (finalCosts M K V)) else none

noncomputable def evaluate (us : List I) : Option ℕ :=
  (terminal M K (run M K us).2).map ((run M K us).1 + ·)

theorem run_nonempty_iff (hb : M.bounded K) (us : List I) :
    (run M K us).2.Nonempty ↔ ∃ xs, M.valid xs ∧ xs.map M.input = us := by
  constructor
  · rintro ⟨⟨q,r⟩,hr⟩
    obtain ⟨xs,hv,hm,_⟩ := run_sound M K us q r hr
    exact ⟨xs,hv,hm⟩
  · intro h
    obtain ⟨xs,hw,hm⟩ := winner_exists M h
    have hw' : M.winner (xs ++ []) := by simpa using hw
    obtain ⟨r,hr,_⟩ := optimal_prefix_retained M K hb xs [] hw'
    exact ⟨(M.state M.start xs,r),by simpa [hm] using hr⟩

theorem evaluate_winner (hb : M.bounded K) {xs : List A} (hw : M.winner xs) :
    evaluate M K (xs.map M.input) = some (M.total M.start xs) := by
  let s := run M K (xs.map M.input)
  have hn : s.2.Nonempty := (run_nonempty_iff M K hb _).mpr ⟨xs,hw.1,rfl⟩
  have hfn : (finalCosts M K s.2).Nonempty := by
    obtain ⟨⟨q,r⟩,hr⟩ := hn
    exact ⟨r.val+M.final q,q,r,hr,rfl⟩
  obtain ⟨q,r,hr,he⟩ := Nat.sInf_mem hfn
  obtain ⟨ys,hy,hym,hys,hyc⟩ := run_sound M K _ q r hr
  have lower := hw.2 ys hy hym
  have hyfull : M.total M.start ys = s.1 + (r.val+M.final q) := by
    simp [Machine.total,hyc,hys,s,Nat.add_assoc]
  have hw' : M.winner (xs ++ []) := by simpa using hw
  obtain ⟨rx,hrx,hcx⟩ := optimal_prefix_retained M K hb xs [] hw'
  have upper : sInf (finalCosts M K s.2) ≤ rx.val+M.final (M.state M.start xs) :=
    Nat.sInf_le ⟨M.state M.start xs,rx,hrx,rfl⟩
  have hxf : M.total M.start xs = s.1 + (rx.val+M.final (M.state M.start xs)) := by
    simp [Machine.total,hcx,s,Nat.add_assoc]
  have eq : s.1+sInf (finalCosts M K s.2) = M.total M.start xs := by omega
  simpa [evaluate,terminal,hn,s] using congrArg some eq

theorem evaluate_none_iff (hb : M.bounded K) (us : List I) :
    evaluate M K us = none ↔ ¬ ∃ xs, M.valid xs ∧ xs.map M.input = us := by
  classical
  simp [evaluate,terminal,← run_nonempty_iff M K hb us]

end WeightedCost
