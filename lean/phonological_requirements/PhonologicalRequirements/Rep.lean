                                                         
namespace PhonologicalRequirements
namespace Rep

structure Node where
  sort : String
  made : Bool
  idx  : Nat
deriving DecidableEq, Repr

structure Struct where
  order : List Node
  real  : List (Node × String)
  assoc : List (Node × Node)
  corr  : Option (List (Node × List Node))

def WF (ref : List Node) (s : Struct) : Prop :=
  s.order.Nodup ∧
  (∀ n, n ∈ s.order → ∃ v, (n, v) ∈ s.real) ∧
  (∀ p, p ∈ s.assoc → p.1 ∈ s.order ∧ p.2 ∈ s.order) ∧
  (∀ n, n ∈ s.order → n.made = false → n ∈ ref) ∧
  (match s.corr with
   | none   => ∀ r, r ∈ ref → r ∈ s.order
   | some c => ∀ n cs, (n, cs) ∈ c → ∀ x, x ∈ cs → x ∈ ref)

def setReal (s : Struct) (p : Node) (v : String) : Struct :=
  { s with real := (p, v) :: s.real }

def insertAt (s : Struct) (i : Nat) (n : Node) (v : String) : Struct :=
  { order := s.order.take i ++ n :: s.order.drop i
    real  := (n, v) :: s.real
    assoc := s.assoc
    corr  := match s.corr with
             | none   => none
             | some c => some ((n, []) :: c) }

def link (s : Struct) (a b : Node) : Struct :=
  { s with assoc := (a, b) :: s.assoc }

def unlink (s : Struct) (a b : Node) : Struct :=
  { s with assoc := s.assoc.filter (fun p => decide (p ≠ (a, b))) }

def rn (f : Nat → Nat) (n : Node) : Node :=
  if n.made then { n with idx := f n.idx } else n

def renameMade (f : Nat → Nat) (s : Struct) : Struct :=
  { order := s.order.map (rn f)
    real  := s.real.map (fun p => (rn f p.1, p.2))
    assoc := s.assoc.map (fun p => (rn f p.1, rn f p.2))
    corr  := s.corr.map (fun c => c.map (fun p => (rn f p.1, p.2))) }

theorem WF_setReal {ref : List Node} {s : Struct} (h : WF ref s) (p : Node) (v : String) :
    WF ref (setReal s p v) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, ?_, h3, h4, h5⟩
  intro n hn
  rcases h2 n hn with ⟨w, hw⟩
  exact ⟨w, List.mem_cons_of_mem _ hw⟩

theorem WF_link {ref : List Node} {s : Struct} (h : WF ref s) {a b : Node}
    (ha : a ∈ s.order) (hb : b ∈ s.order) : WF ref (link s a b) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, ?_, h4, h5⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp'
  · exact ⟨ha, hb⟩
  · exact h3 p hp'

theorem WF_unlink {ref : List Node} {s : Struct} (h : WF ref s) (a b : Node) :
    WF ref (unlink s a b) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, ?_, h4, h5⟩
  intro p hp
  exact h3 p (List.mem_filter.mp hp).1

theorem mem_insert_of_mem {α : Type} {l : List α} {x n : α} (i : Nat) (hx : x ∈ l) :
    x ∈ l.take i ++ n :: l.drop i := by
  have : x ∈ l.take i ++ l.drop i := by rw [List.take_append_drop]; exact hx
  rcases List.mem_append.mp this with h | h
  · exact List.mem_append.mpr (Or.inl h)
  · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h))

theorem mem_of_mem_insert {α : Type} {l : List α} {x n : α} (i : Nat)
    (hx : x ∈ l.take i ++ n :: l.drop i) : x = n ∨ x ∈ l := by
  rcases List.mem_append.mp hx with h | h
  · exact Or.inr (List.mem_of_mem_take h)
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_drop h)

theorem nodup_insert {α : Type} [DecidableEq α] {l : List α} (i : Nat) {n : α}
    (hl : l.Nodup) (hn : n ∉ l) : (l.take i ++ n :: l.drop i).Nodup := by
  have hsplit : (l.take i ++ l.drop i).Nodup := by rw [List.take_append_drop]; exact hl
  rw [List.nodup_append] at hsplit
  rcases hsplit with ⟨ht, hd, hdis⟩
  rw [List.nodup_append]
  refine ⟨ht, ?_, ?_⟩
  · rw [List.nodup_cons]
    refine ⟨?_, hd⟩
    intro hmem; exact hn (List.mem_of_mem_drop hmem)
  · intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · intro heq; exact hn (List.mem_of_mem_take (heq ▸ ha))
    · exact hdis a ha b hb'

theorem WF_insertAt {ref : List Node} {s : Struct} (h : WF ref s) (i : Nat) {n : Node}
    (hmade : n.made = true) (hnew : n ∉ s.order) (v : String) : WF ref (insertAt s i n v) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨nodup_insert i h1 hnew, ?_, ?_, ?_, ?_⟩
  · intro m hm
    rcases mem_of_mem_insert i hm with rfl | hm'
    · exact ⟨v, List.mem_cons.mpr (Or.inl rfl)⟩
    · rcases h2 m hm' with ⟨w, hw⟩
      exact ⟨w, List.mem_cons_of_mem _ hw⟩
  · intro p hp
    rcases h3 p hp with ⟨ha, hb⟩
    exact ⟨mem_insert_of_mem i ha, mem_insert_of_mem i hb⟩
  · intro m hm hlex
    rcases mem_of_mem_insert i hm with rfl | hm'
    · rw [hmade] at hlex; cases hlex
    · exact h4 m hm' hlex
  · cases hc : s.corr with
    | none =>
      simp only [insertAt, hc]
      intro r hr
      have : r ∈ s.order := by
        have h5' := h5; rw [hc] at h5'; exact h5' r hr
      exact mem_insert_of_mem i this
    | some c =>
      simp only [insertAt, hc]
      intro m cs hmc x hx
      rcases List.mem_cons.mp hmc with heq | hmc'
      · cases heq; cases hx
      · have h5' := h5; rw [hc] at h5'; exact h5' m cs hmc' x hx

                                        

def swapList {α : Type} (l : List α) (i : Nat) : List α :=
  l.take i ++ (match l.drop i with
    | a :: b :: rest => b :: a :: rest
    | l' => l')

def swapAt (s : Struct) (i : Nat) : Struct := { s with order := swapList s.order i }

theorem mem_swapTail_iff {α : Type} (l : List α) (x : α) :
    x ∈ (match l with | a :: b :: rest => b :: a :: rest | l' => l') ↔ x ∈ l := by
  cases l with
  | nil => exact Iff.rfl
  | cons a t =>
    cases t with
    | nil => exact Iff.rfl
    | cons b rest =>
      simp only [List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem mem_swapList_iff {α : Type} (l : List α) (i : Nat) (x : α) : x ∈ swapList l i ↔ x ∈ l := by
  unfold swapList
  have hsplit : l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
  rw [List.mem_append, mem_swapTail_iff]
  constructor
  · rintro (h | h)
    · rw [hsplit]; exact List.mem_append.mpr (Or.inl h)
    · rw [hsplit]; exact List.mem_append.mpr (Or.inr h)
  · intro h
    rw [hsplit] at h
    exact List.mem_append.mp h

theorem nodup_swapTail {α : Type} (l : List α) (h : l.Nodup) :
    (match l with | a :: b :: rest => b :: a :: rest | l' => l').Nodup := by
  cases l with
  | nil => exact h
  | cons a t =>
    cases t with
    | nil => exact h
    | cons b rest =>
      rw [List.nodup_cons] at h ⊢
      rcases h with ⟨ha, hd⟩
      rw [List.nodup_cons] at hd ⊢
      rcases hd with ⟨hb, hrest⟩
      refine ⟨?_, ?_, hrest⟩
      · intro hmem
        rcases List.mem_cons.mp hmem with h | h
        · exact ha (h ▸ List.mem_cons.mpr (Or.inl rfl))
        · exact hb h
      · intro hmem; exact ha (List.mem_cons.mpr (Or.inr hmem))

theorem nodup_swapList {α : Type} (l : List α) (i : Nat) (h : l.Nodup) : (swapList l i).Nodup := by
  unfold swapList
  have hsplit : (l.take i ++ l.drop i).Nodup := by rw [List.take_append_drop]; exact h
  rw [List.nodup_append] at hsplit ⊢
  rcases hsplit with ⟨ht, hd, hdis⟩
  exact ⟨ht, nodup_swapTail _ hd, fun x hx y hy => hdis x hx y ((mem_swapTail_iff _ y).mp hy)⟩

theorem WF_swapAt {ref : List Node} {s : Struct} (h : WF ref s) (i : Nat) : WF ref (swapAt s i) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨nodup_swapList _ i h1, ?_, ?_, ?_, ?_⟩
  · intro n hn; exact h2 n ((mem_swapList_iff _ i n).mp hn)
  · intro p hp
    rcases h3 p hp with ⟨ha, hb⟩
    exact ⟨(mem_swapList_iff _ i _).mpr ha, (mem_swapList_iff _ i _).mpr hb⟩
  · intro n hn hlex; exact h4 n ((mem_swapList_iff _ i n).mp hn) hlex
  · simp only [swapAt]
    cases hc : s.corr with
    | none =>
      simp only
      intro r hr
      have h5' := h5; rw [hc] at h5'; simp only at h5'
      exact (mem_swapList_iff _ i r).mpr (h5' r hr)
    | some c =>
      simp only
      have h5' := h5; rw [hc] at h5'; simp only at h5'
      exact h5'

def rep (a n x : Node) : Node := if x = a then n else x

theorem rep_injective_on {a n : Node} {l : List Node} (hn : n ∉ l) :
    ∀ x y, x ∈ l → y ∈ l → rep a n x = rep a n y → x = y := by
  intro x y hx hy h
  unfold rep at h
  by_cases hxa : x = a <;> by_cases hya : y = a <;> simp [hxa, hya] at h
  · rw [hxa, hya]
  · exact absurd (h ▸ hy) hn
  · exact absurd (h.symm ▸ hx) hn
  · exact h

theorem nodup_map_rep {a n : Node} {l : List Node} (hl : l.Nodup) (hn : n ∉ l) : (l.map (rep a n)).Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map]
  have : l.Pairwise (fun x y => x ∈ l → y ∈ l → rep a n x ≠ rep a n y) :=
    hl.imp (fun hne hx hy heq => hne (rep_injective_on hn _ _ hx hy heq))
  exact List.Pairwise.imp_of_mem (fun {x y} hx hy hxy => hxy hx hy) this

theorem mem_map_rep_of_mem {a n x : Node} {l : List Node} (hx : x ∈ l) : rep a n x ∈ l.map (rep a n) :=
  List.mem_map.mpr ⟨x, hx, rfl⟩

theorem rep_eq_of_ne {a n x : Node} (h : x ≠ a) : rep a n x = x := by unfold rep; simp [h]
theorem rep_self (a n : Node) : rep a n a = n := by unfold rep; simp

def fuse (s : Struct) (a b n : Node) (v : String) (cs : List Node) : Struct :=
  { order := (s.order.filter (fun x => decide (x ≠ b))).map (rep a n)
    real  := (n, v) :: s.real
    assoc := s.assoc.map (fun p => (rep a n (rep b n p.1), rep a n (rep b n p.2)))
    corr  := s.corr.map (fun c => (n, cs) :: c) }

theorem WF_fuse {ref : List Node} {s : Struct} (h : WF ref s) {a b n : Node} (v : String) (cs : List Node)
    (hmade : n.made = true) (hnew : n ∉ s.order) (ha : a ∈ s.order) (hab : a ≠ b)
    (hcs : ∀ x, x ∈ cs → x ∈ ref) (hcorr : ∃ c, s.corr = some c) : WF ref (fuse s a b n v cs) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  have hfil : ∀ x, x ∈ s.order.filter (fun x => decide (x ≠ b)) → x ∈ s.order :=
    fun x hx => (List.mem_filter.mp hx).1
  have hmemfil : ∀ x, x ∈ s.order → x ≠ b → x ∈ s.order.filter (fun x => decide (x ≠ b)) :=
    fun x hx hne => List.mem_filter.mpr ⟨hx, by simpa using hne⟩
  have hnew' : n ∉ s.order.filter (fun x => decide (x ≠ b)) := fun hx => hnew (hfil n hx)
  have hna : n ≠ a := fun h => hnew (h ▸ ha)
  have hsurv : ∀ x, x ∈ s.order → rep a n (rep b n x) ∈ (s.order.filter (fun x => decide (x ≠ b))).map (rep a n) := by
    intro x hx
    by_cases hxb : x = b
    · rw [hxb, rep_self, rep_eq_of_ne hna]
      have := mem_map_rep_of_mem (a := a) (n := n) (hmemfil a ha hab)
      rw [rep_self] at this
      exact this
    · rw [rep_eq_of_ne hxb]
      exact mem_map_rep_of_mem (hmemfil x hx hxb)
  have hfilnd : (s.order.filter (fun x => decide (x ≠ b))).Nodup := List.Pairwise.filter _ h1
  refine ⟨nodup_map_rep hfilnd hnew', ?_, ?_, ?_, ?_⟩
  · intro m hm
    rcases List.mem_map.mp hm with ⟨q, hq, rfl⟩
    by_cases hqa : q = a
    · rw [hqa, rep_self]; exact ⟨v, List.mem_cons.mpr (Or.inl rfl)⟩
    · rw [rep_eq_of_ne hqa]
      rcases h2 q (hfil q hq) with ⟨w, hw⟩
      exact ⟨w, List.mem_cons_of_mem _ hw⟩
  · intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    rcases h3 q hq with ⟨hq1, hq2⟩
    exact ⟨hsurv q.1 hq1, hsurv q.2 hq2⟩
  · intro m hm hlex
    rcases List.mem_map.mp hm with ⟨q, hq, rfl⟩
    by_cases hqa : q = a
    · rw [hqa, rep_self] at hlex; rw [hmade] at hlex; cases hlex
    · rw [rep_eq_of_ne hqa] at hlex ⊢
      exact h4 q (hfil q hq) hlex
  · simp only [fuse]
    rcases hcorr with ⟨c, hc⟩
    rw [hc]
    simp only [Option.map]
    intro m ms hmc x hx
    rcases List.mem_cons.mp hmc with heq | hmc'
    · cases heq; exact hcs x hx
    · have h5' := h5; rw [hc] at h5'; simp only at h5'; exact h5' m ms hmc' x hx

def splitAt (s : Struct) (a n1 n2 : Node) (i : Nat) (v1 v2 : String) (cs : List Node) : Struct :=
  { order := (s.order.map (rep a n1)).take i ++ n2 :: (s.order.map (rep a n1)).drop i
    real  := (n1, v1) :: (n2, v2) :: s.real
    assoc := s.assoc.map (fun p => (rep a n1 p.1, rep a n1 p.2))
    corr  := s.corr.map (fun c => (n1, cs) :: (n2, cs) :: c) }

theorem WF_splitAt {ref : List Node} {s : Struct} (h : WF ref s) {a n1 n2 : Node} (i : Nat) (v1 v2 : String)
    (cs : List Node) (hm1 : n1.made = true) (hm2 : n2.made = true) (hn1 : n1 ∉ s.order) (hn2 : n2 ∉ s.order)
    (h12 : n1 ≠ n2) (hcs : ∀ x, x ∈ cs → x ∈ ref) (hcorr : ∃ c, s.corr = some c) :
    WF ref (splitAt s a n1 n2 i v1 v2 cs) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  have hn2' : n2 ∉ s.order.map (rep a n1) := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨q, hq, hqe⟩
    by_cases hqa : q = a
    · rw [hqa, rep_self] at hqe; exact h12 hqe
    · rw [rep_eq_of_ne hqa] at hqe; exact hn2 (hqe ▸ hq)
  refine ⟨nodup_insert i (nodup_map_rep h1 hn1) hn2', ?_, ?_, ?_, ?_⟩
  · intro m hm
    rcases mem_of_mem_insert i hm with rfl | hm'
    · exact ⟨v2, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))⟩
    · rcases List.mem_map.mp hm' with ⟨q, hq, rfl⟩
      by_cases hqa : q = a
      · rw [hqa, rep_self]; exact ⟨v1, List.mem_cons.mpr (Or.inl rfl)⟩
      · rw [rep_eq_of_ne hqa]
        rcases h2 q hq with ⟨w, hw⟩
        exact ⟨w, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)⟩
  · intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    rcases h3 q hq with ⟨hq1, hq2⟩
    exact ⟨mem_insert_of_mem i (mem_map_rep_of_mem hq1), mem_insert_of_mem i (mem_map_rep_of_mem hq2)⟩
  · intro m hm hlex
    rcases mem_of_mem_insert i hm with rfl | hm'
    · rw [hm2] at hlex; cases hlex
    · rcases List.mem_map.mp hm' with ⟨q, hq, rfl⟩
      by_cases hqa : q = a
      · rw [hqa, rep_self] at hlex; rw [hm1] at hlex; cases hlex
      · rw [rep_eq_of_ne hqa] at hlex ⊢; exact h4 q hq hlex
  · simp only [splitAt]
    rcases hcorr with ⟨c, hc⟩
    rw [hc]
    simp only [Option.map]
    intro m ms hmc x hx
    rcases List.mem_cons.mp hmc with heq | hmc'
    · cases heq; exact hcs x hx
    · rcases List.mem_cons.mp hmc' with heq | hmc''
      · cases heq; exact hcs x hx
      · have h5' := h5; rw [hc] at h5'; simp only at h5'; exact h5' m ms hmc'' x hx

theorem rn_made (f : Nat → Nat) (n : Node) : (rn f n).made = n.made := by
  unfold rn; split <;> rfl

theorem rn_lex (f : Nat → Nat) {n : Node} (h : n.made = false) : rn f n = n := by
  unfold rn; rw [h]; rfl

theorem rn_injective (f : Nat → Nat) (hf : ∀ a b, f a = f b → a = b) :
    ∀ a b, rn f a = rn f b → a = b := by
  intro a b h
  cases a with
  | mk sa ma ia =>
  cases b with
  | mk sb mb ib =>
  unfold rn at h
  cases ma <;> cases mb <;> simp at h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · obtain ⟨rfl, h2⟩ := h; rw [hf _ _ h2]

theorem mem_map_rn {f : Nat → Nat} {l : List Node} {n : Node} (h : n ∈ l) : rn f n ∈ l.map (rn f) :=
  List.mem_map.mpr ⟨n, h, rfl⟩

theorem WF_renameMade {ref : List Node} {s : Struct} (h : WF ref s) (f : Nat → Nat)
    (hf : ∀ a b, f a = f b → a = b) (href : ∀ r, r ∈ ref → r.made = false) :
    WF ref (renameMade f s) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (s.order.map (rn f)).Nodup
    unfold List.Nodup at *
    rw [List.pairwise_map]
    exact h1.imp (fun hne heq => hne (rn_injective f hf _ _ heq))
  · intro n hn
    rcases List.mem_map.mp hn with ⟨m, hm, rfl⟩
    rcases h2 m hm with ⟨w, hw⟩
    exact ⟨w, List.mem_map.mpr ⟨(m, w), hw, rfl⟩⟩
  · intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    rcases h3 q hq with ⟨ha, hb⟩
    exact ⟨mem_map_rn ha, mem_map_rn hb⟩
  · intro n hn hlex
    rcases List.mem_map.mp hn with ⟨m, hm, rfl⟩
    have hm' : m.made = false := by rw [rn_made] at hlex; exact hlex
    rw [rn_lex f hm']
    exact h4 m hm hm'
  · cases hc : s.corr with
    | none =>
      simp only [renameMade, hc, Option.map]
      intro r hr
      have h5' := h5; rw [hc] at h5'
      have : rn f r = r := rn_lex f (href r hr)
      rw [← this]
      exact mem_map_rn (h5' r hr)
    | some c =>
      simp only [renameMade, hc, Option.map]
      intro n cs hmc x hx
      rcases List.mem_map.mp hmc with ⟨q, hq, hqe⟩
      have h5' := h5; rw [hc] at h5'
      have hcs : cs = q.2 := by cases hqe; rfl
      rw [hcs] at hx
      exact h5' q.1 q.2 hq x hx

def canon : List Node → Nat → List (Bool × Nat)
  | [], _ => []
  | n :: l, k => if n.made then (true, k) :: canon l (k + 1) else (false, n.idx) :: canon l k

theorem canon_rename (f : Nat → Nat) (l : List Node) : ∀ k, canon (l.map (rn f)) k = canon l k := by
  induction l with
  | nil => intro k; rfl
  | cons n l ih =>
    intro k
    simp only [List.map, canon, rn_made]
    by_cases hm : n.made = true
    · rw [if_pos hm, if_pos hm, ih]
    · have hm' : n.made = false := by cases h : n.made <;> simp_all
      rw [if_neg hm, if_neg hm, ih, rn_lex f hm']

end Rep
end PhonologicalRequirements
