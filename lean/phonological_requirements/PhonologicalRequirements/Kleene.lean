                      
namespace PhonologicalRequirements

inductive K where
  | tt : K
  | ff : K
  | uu : K
deriving DecidableEq, Repr

namespace K

def not : K → K
  | tt => ff
  | ff => tt
  | uu => uu

def and : K → K → K
  | ff, _ => ff
  | _, ff => ff
  | uu, _ => uu
  | _, uu => uu
  | tt, tt => tt

def or : K → K → K
  | tt, _ => tt
  | _, tt => tt
  | uu, _ => uu
  | _, uu => uu
  | ff, ff => ff

def collapse : K → Bool
  | tt => true
  | _  => false

theorem and_uu_of_uu {b : K} (hb : b ≠ ff) : K.and uu b = uu := by
  cases b with
  | tt => rfl
  | ff => exact absurd rfl hb
  | uu => rfl

theorem not_uu_iff {a : K} : K.not a = uu ↔ a = uu := by
  cases a <;> simp [K.not]

end K
end PhonologicalRequirements
