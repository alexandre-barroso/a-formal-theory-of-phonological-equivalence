import PhonologicalGrounding.DeclarationLanguage.Decl
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Prod

namespace PhonologicalGrounding.DeclarationLanguage

variable {σ Seg : Type}

structure Decl (σ Seg : Type) where
  slots : σ → Resolver
  subject : σ → Bool
  activation : Term σ Seg
  consequence : Term σ Seg

abbrev Classifier (Seg : Type) := St Seg → Pos → Cls

def Decl.assign (d : Decl σ Seg) (cls : Classifier Seg) (a : Pos) (st : St Seg) :
    σ → Option Pos :=
  fun s => (d.slots s).resolve a (cls st)

def Decl.readers (d : Decl σ Seg) (cls : Classifier Seg) (a : Pos) (st : St Seg) :
    Readers :=
  readersOf (d.consequence.eval (d.assign cls a st) st)
            (d.activation.eval (d.assign cls a st) st)

def Decl.footprint [Fintype σ] [DecidableEq σ] (d : Decl σ Seg) (a : Pos) : Finset Pos :=
  Finset.univ.biUnion fun s => ((d.slots s).footprint a).toFinset

theorem Decl.mem_footprint [Fintype σ] [DecidableEq σ]
    (d : Decl σ Seg) (a : Pos) (s : σ) {o : Pos}
    (h : o ∈ (d.slots s).footprint a) : o ∈ d.footprint a := by
  simp only [Decl.footprint, Finset.mem_biUnion]
  exact ⟨s, Finset.mem_univ s, by simpa using h⟩

def LocalClassifier (cls : Classifier Seg) : Prop :=
  ∀ (st st' : St Seg) (o : Pos), st o = st' o → cls st o = cls st' o

theorem Decl.readers_congr_of_footprint [Fintype σ] [DecidableEq σ]
    {cls : Classifier Seg} (hloc : LocalClassifier cls)
    (d : Decl σ Seg) (a : Pos) {st st' : St Seg}
    (hagree : ∀ o ∈ d.footprint a, st o = st' o) :
    d.readers cls a st = d.readers cls a st' := by
  have hcls : ∀ (s : σ), ∀ o ∈ (d.slots s).footprint a, cls st o = cls st' o := by
    intro s o ho
    exact hloc st st' o (hagree o (d.mem_footprint a s ho))
  have hα : ∀ s : σ, d.assign cls a st s = d.assign cls a st' s := by
    intro s
    exact (d.slots s).resolve_congr a (hcls s)
  have hst : ∀ (s : σ) (o : Pos), d.assign cls a st s = some o → st o = st' o := by
    intro s o ho
    exact hagree o (d.mem_footprint a s ((d.slots s).resolve_mem_footprint a _ ho))
  simp only [Decl.readers, Term.eval_congr _ hα hst]

structure Locus (σ Seg : Type) where
  decl : Decl σ Seg
  anchor : Pos
  weight : ℚ

                       
def Locus.contribution (L : Locus σ Seg) (cls : Classifier Seg)
    (lam : ℚ) (U st : St Seg) : ℚ :=
  let a := (L.decl.readers cls L.anchor U).marked
  L.weight * (a * (L.decl.readers cls L.anchor st).pressure
              + lam * (1 - a) * (L.decl.readers cls L.anchor st).marked)

def score (loci : List (Locus σ Seg)) (cls : Classifier Seg)
    (lam : ℚ) (U st : St Seg) : ℚ :=
  (loci.map fun L => L.contribution cls lam U st).sum

theorem Locus.contribution_congr [Fintype σ] [DecidableEq σ]
    {cls : Classifier Seg} (hloc : LocalClassifier cls)
    (L : Locus σ Seg) (lam : ℚ) (U : St Seg) {st st' : St Seg}
    (hagree : ∀ o ∈ L.decl.footprint L.anchor, st o = st' o) :
    L.contribution cls lam U st = L.contribution cls lam U st' := by
  simp only [Locus.contribution,
    L.decl.readers_congr_of_footprint hloc L.anchor hagree]

def glue (D : Finset Pos) (s t : St Seg) : St Seg :=
  fun o => if o ∈ D then s o else t o

theorem score_glue_left [Fintype σ] [DecidableEq σ]
    {cls : Classifier Seg} (hloc : LocalClassifier cls)
    (loci : List (Locus σ Seg)) (D : Finset Pos)
    (hscoped : ∀ L ∈ loci, L.decl.footprint L.anchor ⊆ D)
    (lam : ℚ) (U s t : St Seg) :
    score loci cls lam U (glue D s t) = score loci cls lam U s := by
  simp only [score]
  congr 1
  refine List.map_congr_left ?_
  intro L hL
  refine L.contribution_congr hloc lam U ?_
  intro o ho
  simp [glue, hscoped L hL ho]

theorem score_glue_right [Fintype σ] [DecidableEq σ]
    {cls : Classifier Seg} (hloc : LocalClassifier cls)
    (loci : List (Locus σ Seg)) (D E : Finset Pos) (hDE : Disjoint D E)
    (hscoped : ∀ L ∈ loci, L.decl.footprint L.anchor ⊆ E)
    (lam : ℚ) (U s t : St Seg) :
    score loci cls lam U (glue D s t) = score loci cls lam U t := by
  simp only [score]
  congr 1
  refine List.map_congr_left ?_
  intro L hL
  refine L.contribution_congr hloc lam U ?_
  intro o ho
  have hoE : o ∈ E := hscoped L hL ho
  have : o ∉ D := fun hoD => (Finset.disjoint_left.mp hDE hoD) hoE
  simp [glue, this]

theorem score_append (l₁ l₂ : List (Locus σ Seg)) (cls : Classifier Seg)
    (lam : ℚ) (U st : St Seg) :
    score (l₁ ++ l₂) cls lam U st
      = score l₁ cls lam U st + score l₂ cls lam U st := by
  simp [score, List.map_append, List.sum_append]

theorem score_factorises [Fintype σ] [DecidableEq σ]
    {cls : Classifier Seg} (hloc : LocalClassifier cls)
    (lociU lociV : List (Locus σ Seg)) (D E : Finset Pos) (hDE : Disjoint D E)
    (hU : ∀ L ∈ lociU, L.decl.footprint L.anchor ⊆ D)
    (hV : ∀ L ∈ lociV, L.decl.footprint L.anchor ⊆ E)
    (lam : ℚ) (U s t : St Seg) :
    score (lociU ++ lociV) cls lam U (glue D s t)
      = score lociU cls lam U s + score lociV cls lam U t := by
  rw [score_append, score_glue_left hloc lociU D hU lam U s t,
    score_glue_right hloc lociV D E hDE hV lam U s t]

theorem isMin_prod_iff {α β : Type*} (f : α → ℚ) (g : β → ℚ) (a : α) (b : β) :
    (∀ x y, f a + g b ≤ f x + g y) ↔ ((∀ x, f a ≤ f x) ∧ ∀ y, g b ≤ g y) := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun y => ?_⟩
    · have := h x b; linarith
    · have := h a y; linarith
  · rintro ⟨hf, hg⟩ x y
    have := hf x; have := hg y; linarith

theorem argmin_prod_eq {α β : Type*} (f : α → ℚ) (g : β → ℚ) :
    {p : α × β | ∀ q : α × β, f p.1 + g p.2 ≤ f q.1 + g q.2}
      = {a | ∀ x, f a ≤ f x} ×ˢ {b | ∀ y, g b ≤ g y} := by
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_prod]
  constructor
  · intro h
    exact (isMin_prod_iff f g a b).1 (fun x y => h (x, y))
  · rintro ⟨ha, hb⟩ ⟨x, y⟩
    exact (isMin_prod_iff f g a b).2 ⟨ha, hb⟩ x y

theorem noninterference [Fintype σ] [DecidableEq σ]
    {cls : Classifier Seg} (hloc : LocalClassifier cls)
    (lociU lociV : List (Locus σ Seg)) (D E : Finset Pos) (hDE : Disjoint D E)
    (hU : ∀ L ∈ lociU, L.decl.footprint L.anchor ⊆ D)
    (hV : ∀ L ∈ lociV, L.decl.footprint L.anchor ⊆ E)
    (lam : ℚ) (U : St Seg) (SU SV : Type)
    (embU : SU → St Seg) (embV : SV → St Seg) :
    (∀ s t, score (lociU ++ lociV) cls lam U (glue D (embU s) (embV t))
        = score lociU cls lam U (embU s) + score lociV cls lam U (embV t))
    ∧ {p : SU × SV |
          ∀ q : SU × SV,
            score (lociU ++ lociV) cls lam U (glue D (embU p.1) (embV p.2))
              ≤ score (lociU ++ lociV) cls lam U (glue D (embU q.1) (embV q.2))}
        = {s | ∀ x, score lociU cls lam U (embU s)
                      ≤ score lociU cls lam U (embU x)} ×ˢ
          {t | ∀ y, score lociV cls lam U (embV t)
                      ≤ score lociV cls lam U (embV y)} := by
  have hsum : ∀ s t, score (lociU ++ lociV) cls lam U (glue D (embU s) (embV t))
      = score lociU cls lam U (embU s) + score lociV cls lam U (embV t) :=
    fun s t => score_factorises hloc lociU lociV D E hDE hU hV lam U (embU s) (embV t)
  refine ⟨hsum, ?_⟩
  have := argmin_prod_eq (fun s : SU => score lociU cls lam U (embU s))
    (fun t : SV => score lociV cls lam U (embV t))
  simpa [hsum] using this

end PhonologicalGrounding.DeclarationLanguage
