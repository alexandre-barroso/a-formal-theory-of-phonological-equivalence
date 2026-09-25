                                      
import PhonologicalGrounding.DeclarationLanguage.Scope

namespace PhonologicalGrounding.DeclarationLanguage

variable {σ Seg : Type}

def overwrite (P : Finset Pos) (w s : St Seg) : St Seg :=
  fun o => if o ∈ P then w o else s o

theorem footprintEq_overwrite [Fintype σ] [DecidableEq σ]
    (d : Decl σ Seg) (a : Pos) {s t : St Seg}
    (h : ∀ o ∈ d.footprint a, s o = t o) (P : Finset Pos) (w : St Seg) :
    ∀ o ∈ d.footprint a, overwrite P w s o = overwrite P w t o := by
  intro o ho
  by_cases hP : o ∈ P <;> simp [overwrite, hP, h o ho]

theorem footprintEq_readers_congr_in_context [Fintype σ] [DecidableEq σ]
    {cls : Classifier Seg} (hloc : LocalClassifier cls)
    (d : Decl σ Seg) (a : Pos) {s t : St Seg}
    (h : ∀ o ∈ d.footprint a, s o = t o) :
    ∀ (ops : List (Finset Pos × St Seg)),
      d.readers cls a (ops.foldl (fun st op => overwrite op.1 op.2 st) s)
        = d.readers cls a (ops.foldl (fun st op => overwrite op.1 op.2 st) t) := by
  intro ops
  induction ops generalizing s t with
  | nil => exact d.readers_congr_of_footprint hloc a h
  | cons op rest ih =>
      simpa using ih (footprintEq_overwrite d a h op.1 op.2)

structure Record (σ Seg : Type) where
  activation : Bool
  carrier : Pos → Seg
  weight : ℚ

theorem contribution_determined_by_record [Fintype σ] [DecidableEq σ]
    {cls : Classifier Seg} (hloc : LocalClassifier cls)
    (d : Decl σ Seg) (a : Pos) (w lam : ℚ) {U U' s t : St Seg}
    (hU : ∀ o ∈ d.footprint a, U o = U' o)
    (hs : ∀ o ∈ d.footprint a, s o = t o) :
    (Locus.mk d a w).contribution cls lam U s
      = (Locus.mk d a w).contribution cls lam U' t := by
  simp only [Locus.contribution,
    d.readers_congr_of_footprint hloc a hU,
    d.readers_congr_of_footprint hloc a hs]

end PhonologicalGrounding.DeclarationLanguage
