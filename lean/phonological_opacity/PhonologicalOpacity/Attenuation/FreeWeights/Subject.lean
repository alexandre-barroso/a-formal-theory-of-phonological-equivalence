import PhonologicalOpacity.Attenuation.FreeWeights.Selection
namespace FreeWeights
open Retained Deletion

def subjectPair (u : Input) (i : Nat) : Nat × Nat :=
  let s := expand u i
  let rows := (positions u).map fun q =>
    let r := read u s 5 q
    let initial := read u u.origin 5 q
    let next := nextLive u s q
    let defined := next.any fun j => word u j == word u q + 1 && samePhrase u q j
    let p := defined && !r.good
    let retained := initial.context && initial.defined && !initial.good &&
      next == nextLive u u.origin q
    (if p && retained then 1 else 0, if p && !retained && r.context then 1 else 0)
  ((rows.map Prod.fst).sum, (rows.map Prod.snd).sum)

def subjectCoefficients (u : Input) (i : Nat) : List (Nat × Nat) :=
  let c := coefficients u 0 i
  let a := subjectPair u i
  if a = c[5]! then c else c.set 5 a

noncomputable def subjectPressure (u : Input) (w : Fin 9 → ℝ) (l : ℝ) (i : Nat) : ℝ :=
  ∑ k : Fin 9, w k * (((subjectCoefficients u i)[k.val]!.1 : ℝ) +
    l * ((subjectCoefficients u i)[k.val]!.2 : ℝ))

def subjectPolynomial (u : Input) (i : Nat) : Polynomial := polynomialOf (subjectCoefficients u i)

theorem subject_expansion (u : Input) (i : Nat) (l : ℝ) :
    subjectPressure u (witness l) l i = (subjectPolynomial u i).eval l :=
  (polynomial_expansion (subjectCoefficients u i) l).symm

theorem unchanged_pressure (u : Input) (i : Nat) (w : Fin 9 → ℝ) (l : ℝ)
    (h : subjectPair u i = (coefficients u 0 i)[5]!) :
    subjectPressure u w l i = pressure u w l i := by
  simp only [subjectPressure, subjectCoefficients, h, ↓reduceIte, pressure, realPressure]

def checkTransferRow (u : Input) (g : Polynomial) (correct : List Nat) (i : Nat) : Bool :=
  if i ∈ correct then true
  else if subjectPair u i = (coefficients u 0 i)[5]! then true
  else strictRow (subjectPolynomial u i) g

def checkTransferBlock (u : Input) (g : Polynomial) (correct : List Nat) (b : Nat) : Bool :=
  (List.range 169).all fun j => checkTransferRow u g correct (169*b+j)

def checkTransferAll (u : Input) (g : Polynomial) (correct : List Nat) : Bool :=
  (carrier u).all (checkTransferRow u g correct)

theorem assembleTransfer {u : Input} {g : Polynomial} {correct : List Nat} {n : Nat}
    (hn : 13^u.focal.length = 169*n)
    (h : ∀ b < n, checkTransferBlock u g correct b = true) : checkTransferAll u g correct = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi' : i < 169*n := by simpa [carrier,hn] using hi
  have hb : i/169 < n := by omega
  have hj : i%169 < 169 := Nat.mod_lt i (by decide)
  have hx := List.all_eq_true.mp (h (i/169) hb) (i%169) (List.mem_range.mpr hj)
  have he : 169*(i/169)+i%169=i := by omega
  simpa only [he] using hx

theorem subject_strict_separation {u : Input} {g : Polynomial} {correct : List Nat} {goal : Nat}
    (hc : checkAll u g correct = true) (ht : checkTransferAll u g correct = true)
    (hp : polynomial u goal = g)
    (hg : subjectPair u goal = (coefficients u 0 goal)[5]!)
    (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2)
    (i : Nat) (hi : i ∈ carrier u) (hw : i ∉ correct) :
    subjectPressure u (witness l) l goal < subjectPressure u (witness l) l i := by
  have hx := List.all_eq_true.mp ht i hi
  rw [unchanged_pressure u goal _ l hg]
  by_cases he : subjectPair u i = (coefficients u 0 i)[5]!
  · rw [unchanged_pressure u i _ l he]
    exact strict_separation hc hp l h0 h1 i hi hw
  · have hr : strictRow (subjectPolynomial u i) g = true := by
      simpa only [checkTransferRow, if_neg hw, if_neg he] using hx
    rw [pressure_expansion, subject_expansion, hp]
    exact strictRow_sound hr l h0 h1

theorem subject_certificate_exclusive {u : Input} {g : Polynomial} {correct : List Nat}
    {goal : Nat} {out : String} (hc : checkAll u g correct = true)
    (ht : checkTransferAll u g correct = true) (hp : polynomial u goal = g)
    (hu : subjectPair u goal = (coefficients u 0 goal)[5]!)
    (hg : goal ∈ carrier u) (hf : fiber u out = correct)
    (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive u (subjectPressure u (witness l) l) out := by
  apply exclusive_of_separation u _ out goal hg
  intro i hi hwrong
  have hnot : i ∉ correct := by
    intro hc
    rw [← hf] at hc
    have hh : realize u i = out := by simpa [fiber] using (List.mem_filter.mp hc).2
    exact hwrong hh
  exact subject_strict_separation hc ht hp hu l h0 h1 i hi hnot
end FreeWeights
