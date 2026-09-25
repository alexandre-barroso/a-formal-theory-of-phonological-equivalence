import PhonologicalRequirements.Discipline

namespace PhonologicalRequirements
namespace Registered
open Discipline

def total0 : String → Bool := fun s => ["Or"].contains s
def set0 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Rel", .subject, .step, some "succ", "next_word_same_phrase|same=phrase|delta=word:1|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p", "Rel", .trigger, .step, some "succ", "prev_word_same_phrase|same=phrase|delta=word:-1|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["p", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nr", "Rel", .trigger, .step, some "succ", "next_word_same_phrase|same=phrase|delta=word:1|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nl", "Rel", .trigger, .step, some "succ", "prev_word_same_phrase|same=phrase|delta=word:-1|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["nl", "nr", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"src", "Or", .trigger, .search, some "succ", "same_phrase_strictly_later_word|same=phrase|delta=|min=word:1", (1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["src", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false }]

def total1 : String → Bool := fun s => ["Or"].contains s
def set1 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Rel", .subject, .step, some "succ", "same_prosodic_word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Rel", .subject, .step, some "succ", "same_prosodic_word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false }]

def total2 : String → Bool := fun s => ["Or"].contains s
def set2 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Rel", .subject, .step, some "succ", "same_prosodic_word|same=word|delta=|min=", (1 : Int), none, "skip", "witness", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Rel", .subject, .step, some "succ", "same_prosodic_word|same=word|delta=|min=", (1 : Int), none, "skip", "witness", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false }]

def total3 : String → Bool := fun s => ["Or"].contains s
def set3 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Rel", .subject, .step, some "succ", "same_prosodic_word|same=word|delta=|min=", (1 : Int), none, "skip", "reference", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Rel", .subject, .step, some "succ", "same_prosodic_word|same=word|delta=|min=", (1 : Int), none, "skip", "reference", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false }]

def total4 : String → Bool := fun s => ["Or"].contains s
def set4 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nrv", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", [("red", "1")]⟩],
    actSlots := ["t"], consSlots := ["nrv"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"c", "Or", .subject, .corr, none, "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["c"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"c", "Or", .subject, .corr, none, "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["c", "t"], consSlots := ["c", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"k", "Or", .subject, .corr, none, "word|same=word|delta=|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["k"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1", "n2", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"o", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n1", "n2", "o", "t"], consSlots := ["n1", "n2", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n1", "n2", "t"], consSlots := ["t"], override := false }]

def total5 : String → Bool := fun s => ["Or"].contains s
def set5 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nrv", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", [("red", "1")]⟩],
    actSlots := ["t"], consSlots := ["nrv"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"c", "Or", .subject, .corr, none, "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["c"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"nv", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1", "n2", "nv", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"c", "Or", .subject, .corr, none, "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["c", "t"], consSlots := ["c", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"k", "Or", .subject, .corr, none, "word|same=word|delta=|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["k"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n3", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1", "n2", "n3", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1", "n2", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"pv", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩,
      ⟨"p1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["p1", "pv", "t"], consSlots := ["p1", "pv", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n1", "n2", "t"], consSlots := ["t"], override := false }]

def total6 : String → Bool := fun s => ["Or"].contains s
def set6 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "phrase|same=phrase|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "phrase|same=phrase|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n1", "n2", "t"], consSlots := ["n2"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nv", "Or", .subject, .step, some "succ", "phrase|same=phrase|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["nv", "t"], consSlots := ["nv"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p1", "Or", .subject, .step, some "succ", "phrase|same=phrase|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "phrase|same=phrase|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n1", "p1", "t"], consSlots := ["n1"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false }]

def total7 : String → Bool := fun s => ["Or"].contains s
def set7 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["t"], override := false }]

def total8 : String → Bool := fun s => ["Or"].contains s
def set8 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "r1", "t"], override := false }]

def total9 : String → Bool := fun s => ["Or"].contains s
def set9 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "t"], override := false }]

def total10 : String → Bool := fun s => ["Or"].contains s
def set10 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["r1", "t"], override := false }]

def total11 : String → Bool := fun s => ["Or"].contains s
def set11 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["t"], override := false }]

def total12 : String → Bool := fun s => ["Or"].contains s
def set12 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "r1", "t"], override := false }]

def total13 : String → Bool := fun s => ["Or"].contains s
def set13 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "t"], override := false }]

def total14 : String → Bool := fun s => ["Or"].contains s
def set14 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["r1", "t"], override := false }]

def total15 : String → Bool := fun s => ["Or"].contains s
def set15 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "r2", "t"], consSlots := ["t"], override := false }]

def total16 : String → Bool := fun s => ["Or"].contains s
def set16 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "r2", "t"], consSlots := ["r1", "r2", "t"], override := false }]

def total17 : String → Bool := fun s => ["Or"].contains s
def set17 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "r2", "t"], consSlots := ["t"], override := false }]

def total18 : String → Bool := fun s => ["Or"].contains s
def set18 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "r2", "t"], consSlots := ["r1", "r2", "t"], override := false }]

def total19 : String → Bool := fun s => ["Or"].contains s
def set19 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "r2", "t"], consSlots := ["t"], override := false }]

def total20 : String → Bool := fun s => ["Or"].contains s
def set20 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "r2", "t"], consSlots := ["r1", "r2", "t"], override := false }]

def total21 : String → Bool := fun s => ["Or"].contains s
def set21 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "r2", "t"], consSlots := ["t"], override := false }]

def total22 : String → Bool := fun s => ["Or"].contains s
def set22 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "r2", "t"], consSlots := ["r1", "r2", "t"], override := false }]

def total23 : String → Bool := fun s => ["Or"].contains s
def set23 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["t"], override := false }]

def total24 : String → Bool := fun s => ["Or"].contains s
def set24 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "r1", "t"], override := false }]

def total25 : String → Bool := fun s => ["Or"].contains s
def set25 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "t"], override := false }]

def total26 : String → Bool := fun s => ["Or"].contains s
def set26 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["r1", "t"], override := false }]

def total27 : String → Bool := fun s => ["Or"].contains s
def set27 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["t"], override := false }]

def total28 : String → Bool := fun s => ["Or"].contains s
def set28 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "r1", "t"], override := false }]

def total29 : String → Bool := fun s => ["Or"].contains s
def set29 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "t"], override := false }]

def total30 : String → Bool := fun s => ["Or"].contains s
def set30 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["r1", "t"], override := false }]

def total31 : String → Bool := fun s => ["Or"].contains s
def set31 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["t"], override := false }]

def total32 : String → Bool := fun s => ["Or"].contains s
def set32 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "r1", "t"], override := false }]

def total33 : String → Bool := fun s => ["Or"].contains s
def set33 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "t"], override := false }]

def total34 : String → Bool := fun s => ["Or"].contains s
def set34 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["r1", "t"], override := false }]

def total35 : String → Bool := fun s => ["Or"].contains s
def set35 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["t"], override := false }]

def total36 : String → Bool := fun s => ["Or"].contains s
def set36 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["l1", "l2", "r1", "r2", "t"], override := false }]

def total37 : String → Bool := fun s => ["Or"].contains s
def set37 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["l1", "l2", "t"], override := false }]

def total38 : String → Bool := fun s => ["Or"].contains s
def set38 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["r1", "r2", "t"], override := false }]

def total39 : String → Bool := fun s => ["Or"].contains s
def set39 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false }]

def total40 : String → Bool := fun s => ["Or"].contains s
def set40 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "t"], consSlots := ["l1", "l2", "r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false }]

def total41 : String → Bool := fun s => ["Or"].contains s
def set41 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "t"], consSlots := ["l1", "l2", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false }]

def total42 : String → Bool := fun s => ["Or"].contains s
def set42 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false }]

def total43 : String → Bool := fun s => ["Or"].contains s
def set43 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false }]

def total44 : String → Bool := fun s => ["Or"].contains s
def set44 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false }]

def total45 : String → Bool := fun s => ["Or"].contains s
def set45 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false }]

def total46 : String → Bool := fun s => ["Or"].contains s
def set46 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false }]

def total47 : String → Bool := fun s => ["Or"].contains s
def set47 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["t"], override := false }]

def total48 : String → Bool := fun s => ["Or"].contains s
def set48 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["l1", "l2", "r1", "r2", "t"], override := false }]

def total49 : String → Bool := fun s => ["Or"].contains s
def set49 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["l1", "l2", "t"], override := false }]

def total50 : String → Bool := fun s => ["Or"].contains s
def set50 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["r1", "r2", "t"], override := false }]

def total51 : String → Bool := fun s => ["Or"].contains s
def set51 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["t"], override := false }]

def total52 : String → Bool := fun s => ["Or"].contains s
def set52 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["l1", "l2", "r1", "r2", "t"], override := false }]

def total53 : String → Bool := fun s => ["Or"].contains s
def set53 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["l1", "l2", "t"], override := false }]

def total54 : String → Bool := fun s => ["Or"].contains s
def set54 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["r1", "r2", "t"], override := false }]

def total55 : String → Bool := fun s => ["Or"].contains s
def set55 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["t"], override := false }]

def total56 : String → Bool := fun s => ["Or"].contains s
def set56 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["l1", "l2", "r1", "r2", "t"], override := false }]

def total57 : String → Bool := fun s => ["Or"].contains s
def set57 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["l1", "l2", "t"], override := false }]

def total58 : String → Bool := fun s => ["Or"].contains s
def set58 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "r1", "r2", "t"], consSlots := ["r1", "r2", "t"], override := false }]

def total59 : String → Bool := fun s => ["Or"].contains s
def set59 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["t"], override := false }]

def total60 : String → Bool := fun s => ["Or"].contains s
def set60 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["l1", "t"], override := false }]

def total61 : String → Bool := fun s => ["Or"].contains s
def set61 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["l1", "t"], override := false }]

def total62 : String → Bool := fun s => ["Or"].contains s
def set62 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["t"], override := false }]

def total63 : String → Bool := fun s => ["Or"].contains s
def set63 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["t"], override := false }]

def total64 : String → Bool := fun s => ["Or"].contains s
def set64 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["l1", "t"], override := false }]

def total65 : String → Bool := fun s => ["Or"].contains s
def set65 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["l1", "t"], override := false }]

def total66 : String → Bool := fun s => ["Or"].contains s
def set66 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["t"], override := false }]

def total67 : String → Bool := fun s => ["Or"].contains s
def set67 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "t"], consSlots := ["t"], override := false }]

def total68 : String → Bool := fun s => ["Or"].contains s
def set68 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "t"], consSlots := ["l1", "l2", "t"], override := false }]

def total69 : String → Bool := fun s => ["Or"].contains s
def set69 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "t"], consSlots := ["l1", "l2", "t"], override := false }]

def total70 : String → Bool := fun s => ["Or"].contains s
def set70 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "t"], consSlots := ["t"], override := false }]

def total71 : String → Bool := fun s => ["Or"].contains s
def set71 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "t"], consSlots := ["t"], override := false }]

def total72 : String → Bool := fun s => ["Or"].contains s
def set72 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "t"], consSlots := ["l1", "l2", "t"], override := false }]

def total73 : String → Bool := fun s => ["Or"].contains s
def set73 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "t"], consSlots := ["l1", "l2", "t"], override := false }]

def total74 : String → Bool := fun s => ["Or"].contains s
def set74 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "l2", "t"], consSlots := ["t"], override := false }]

def total75 : String → Bool := fun s => ["Or"].contains s
def set75 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["t"], override := false }]

def total76 : String → Bool := fun s => ["Or"].contains s
def set76 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "r1", "t"], override := false }]

def total77 : String → Bool := fun s => ["Or"].contains s
def set77 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["l1", "t"], override := false }]

def total78 : String → Bool := fun s => ["Or"].contains s
def set78 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "r1", "t"], consSlots := ["r1", "t"], override := false }]

def total79 : String → Bool := fun s => ["Or"].contains s
def set79 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false }]

def total80 : String → Bool := fun s => ["Or"].contains s
def set80 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["l1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false }]

def total81 : String → Bool := fun s => ["Or"].contains s
def set81 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["l1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false }]

def total82 : String → Bool := fun s => ["Or"].contains s
def set82 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false }]

def total83 : String → Bool := fun s => ["Or"].contains s
def set83 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false }]

def total84 : String → Bool := fun s => ["Or"].contains s
def set84 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["l1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false }]

def total85 : String → Bool := fun s => ["Or"].contains s
def set85 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["l1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false }]

def total86 : String → Bool := fun s => ["Or"].contains s
def set86 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false }]

def total87 : String → Bool := fun s => ["Or"].contains s
def set87 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false }]

def total88 : String → Bool := fun s => ["Or"].contains s
def set88 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false }]

def total89 : String → Bool := fun s => ["Or"].contains s
def set89 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["t"], override := false }]

def total90 : String → Bool := fun s => ["Or"].contains s
def set90 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["r1", "t"], consSlots := ["r1", "t"], override := false }]

def total91 : String → Bool := fun s => ["Or"].contains s
def set91 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"sla", "Or", .subject, .search, none, "word|same=word|delta=|min=", (-1 : Int), some "stressed", "skip", "dynamic", [("accd", "1")]⟩,
      ⟨"sra", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "stressed", "skip", "dynamic", [("accd", "1")]⟩],
    actSlots := ["t"], consSlots := ["sla", "sra", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n1", "n2", "t"], consSlots := ["n1", "n2", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n1", "n2", "t"], consSlots := ["n1", "n2", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"sr", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "stressed", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["sr", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["p1", "t"], consSlots := ["n1", "p1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nv", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1", "n2", "nv", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["p1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nv", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩,
      ⟨"nv2", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩,
      ⟨"nvn1", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"nvn2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1", "n2", "nv", "nv2", "nvn1", "nvn2", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"dr", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", [("acc", "2")]⟩],
    actSlots := ["t"], consSlots := ["dr", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n1", "t"], consSlots := ["n1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"pv", "Or", .subject, .search, none, "word|same=word|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩,
      ⟨"nv", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["nv", "pv", "t"], consSlots := ["nv", "pv", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"n3", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n1", "n2", "n3", "t"], consSlots := ["n1", "n2", "n3", "t"], override := false }]

def total92 : String → Bool := fun s => ["Syl"].contains s
def set92 : List Decl := [
  { slots := [⟨"t", "Syl", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Syl", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Syl", .subject, .step, some "succ", "phrase|same=phrase|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Syl", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p", "Syl", .trigger, .step, some "succ", "phrase|same=phrase|delta=|min=", (-1 : Int), some "present", "skip", "reference", []⟩],
    actSlots := ["p", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Syl", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Syl", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Syl", .subject, .step, some "succ", "phrase|same=phrase|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Syl", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Syl", .subject, .step, some "succ", "phrase|same=phrase|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Syl", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Syl", .subject, .step, some "succ", "phrase|same=phrase|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false }]

def total93 : String → Bool := fun s => ["Syl", "Tone"].contains s
def set93 : List Decl := [
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n2", "Tone", .subject, .stepof, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["n1", "n2"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Syl", .trigger, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (-1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["h", "p1", "t"], consSlots := ["n1", "p1", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n1", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n1", "t"], consSlots := ["n1", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Syl", .trigger, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["h", "t"], consSlots := ["n1", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["n1"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"q1", "Tone", .subject, .search, none, "previous syllable|same=phrase|delta=syll:-1|min=", (-1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"q0", "Tone", .subject, .stepof, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n1", "t"], consSlots := ["n1", "q0", "q1", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"q1", "Tone", .subject, .search, none, "previous syllable|same=phrase|delta=syll:-1|min=", (-1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"q0", "Tone", .subject, .stepof, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n1", "t"], consSlots := ["n1", "q0", "q1", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"q1", "Tone", .subject, .search, none, "previous syllable|same=phrase|delta=syll:-1|min=", (-1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"q0", "Tone", .subject, .stepof, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["q0", "q1", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"x1", "Tone", .subject, .search, none, "next syllable|same=phrase|delta=syll:1|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"x2", "Tone", .subject, .stepof, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t", "x1", "x2"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (-1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["n1", "p1", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"q1", "Tone", .subject, .search, none, "previous syllable|same=phrase|delta=syll:-1|min=", (-1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"q0", "Tone", .subject, .stepof, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n1", "t"], consSlots := ["n1", "q0", "q1", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"x1", "Tone", .subject, .search, none, "next syllable|same=phrase|delta=syll:1|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"x2", "Tone", .subject, .stepof, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n1", "t"], consSlots := ["n1", "t", "x1", "x2"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"x1", "Tone", .subject, .search, none, "next syllable|same=phrase|delta=syll:1|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"x2", "Tone", .subject, .stepof, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n1", "t"], consSlots := ["n1", "t", "x1", "x2"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n1", "Tone", .subject, .step, some "tsucc", "same syllable|same=phrase,syll|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["n1", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Syl", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"a", "Tone", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["a"], override := false }]

def total94 : String → Bool := fun s => ["Or"].contains s
def set94 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nd", "Or", .trigger, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["nd", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false }]

def total95 : String → Bool := fun s => ["Or"].contains s
def set95 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nx", "Or", .trigger, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"pv", "Or", .trigger, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["nx", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nx", "Or", .trigger, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"pv", "Or", .trigger, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["nx", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nx", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["nx", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false }]

def total96 : String → Bool := fun s => ["Or"].contains s
def set96 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nx", "Or", .subject, .step, some "succ", "phrase|same=phrase|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["nx", "t"], consSlots := ["nx", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nx", "Or", .trigger, .step, some "succ", "phrase|same=phrase|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["nx", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false }]

def total97 : String → Bool := fun s => ["Acc", "Or"].contains s
def set97 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"pl", "Or", .subject, .step, some "succ", "prosodic word|same=word,pwd|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["pl", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l", "Or", .subject, .search, none, "word|same=word|delta=|min=", (-1 : Int), some "stressed", "skip", "dynamic", []⟩,
      ⟨"al", "Acc", .subject, .assocof, some "assoc", "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["al", "l"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l", "Or", .subject, .search, none, "word|same=word|delta=|min=", (-1 : Int), some "stressed", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["l"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nr", "Or", .subject, .step, some "succ", "prosodic word|same=word,pwd|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["nr", "t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .trigger, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"dr", "Or", .trigger, .search, none, "later-attached|same=word|delta=|min=rank:1", (1 : Int), none, "skip", "dynamic", [("dele", "1")]⟩,
      ⟨"dl", "Or", .trigger, .search, none, "later-attached|same=word|delta=|min=rank:1", (-1 : Int), none, "skip", "dynamic", [("dele", "1")]⟩],
    actSlots := ["dl", "dr", "hr", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .trigger, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"dr", "Or", .trigger, .stepof, some "succ", "later-attached|same=word|delta=|min=rank:1", (1 : Int), some "moraic", "skip", "dynamic", [("delx", "1")]⟩,
      ⟨"dl", "Or", .trigger, .stepof, some "succ", "later-attached|same=word|delta=|min=rank:1", (-1 : Int), some "moraic", "skip", "dynamic", [("delx", "1")]⟩],
    actSlots := ["dl", "dr", "hr", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"dr", "Or", .subject, .search, none, "later-attached|same=word|delta=|min=rank:1", (1 : Int), none, "skip", "dynamic", [("exp", "1")]⟩,
      ⟨"dl", "Or", .subject, .search, none, "later-attached|same=word|delta=|min=rank:1", (-1 : Int), none, "skip", "dynamic", [("exp", "1")]⟩],
    actSlots := ["dl", "dr", "hr", "t"], consSlots := ["dl", "dr", "h", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nx", "Or", .trigger, .step, some "succ", "later-attached|same=word|delta=|min=rank:1", (1 : Int), some "nuclear", "skip", "dynamic", [("prea", "1")]⟩,
      ⟨"px", "Or", .trigger, .step, some "succ", "later-attached|same=word|delta=|min=rank:1", (-1 : Int), some "nuclear", "skip", "dynamic", [("prea", "1")]⟩],
    actSlots := ["nx", "px"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"nx", "Or", .trigger, .step, some "succ", "later-attached|same=word|delta=|min=rank:1", (1 : Int), some "nuclear", "skip", "dynamic", [("preb", "1")]⟩,
      ⟨"px", "Or", .trigger, .step, some "succ", "later-attached|same=word|delta=|min=rank:1", (-1 : Int), some "nuclear", "skip", "dynamic", [("preb", "1")]⟩],
    actSlots := ["nx", "px"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .trigger, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hn", "Or", .subject, .stepof, some "succ", "prosodic word|same=word,pwd|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩,
      ⟨"dr", "Or", .subject, .search, none, "later-attached|same=word|delta=|min=rank:1", (1 : Int), none, "skip", "dynamic", [("shf", "1")]⟩,
      ⟨"dl", "Or", .subject, .search, none, "later-attached|same=word|delta=|min=rank:1", (-1 : Int), none, "skip", "dynamic", [("shf", "1")]⟩],
    actSlots := ["dl", "dr", "hr", "t"], consSlots := ["dl", "dr", "h", "hn", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l", "Or", .subject, .search, none, "word|same=word|delta=|min=", (-1 : Int), some "stressed", "skip", "dynamic", []⟩,
      ⟨"r", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "stressed", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["l", "r", "t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"pl", "Or", .trigger, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩,
      ⟨"r", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), some "stressed", "skip", "dynamic", []⟩],
    actSlots := ["pl", "t"], consSlots := ["r", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"at", "Acc", .trigger, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"pl", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["at", "t"], consSlots := ["pl"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .trigger, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["h", "hr", "t"], consSlots := ["h", "t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["hr", "t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["hr", "t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .trigger, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"pm", "Or", .trigger, .stepof, some "succ", "same morph|same=morph|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["hr", "pm", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"pl", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["pl", "t"], override := false }]

def total98 : String → Bool := fun s => ["Or"].contains s
def set98 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Or", .subject, .search, none, "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["n"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"z", "Or", .trigger, .search, none, "initial|same=|delta=init:1|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t", "z"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"r", "Or", .subject, .search, none, "root|same=|delta=side:-1|min=", (-1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"f", "Or", .trigger, .search, none, "final|same=|delta=fin:1|min=", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["f", "r", "t"], consSlots := ["r", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"z", "Or", .trigger, .search, none, "root|same=|delta=side:1|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"b", "Or", .trigger, .search, none, "word|same=word|delta=|min=", (1 : Int), some "nonhigh", "skip", "dynamic", []⟩,
      ⟨"q", "Or", .trigger, .search, none, "initial|same=|delta=init:1|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["b", "q", "t", "z"], consSlots := ["t"], override := false }]

def total99 : String → Bool := fun s => ["Or"].contains s
def set99 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"a", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "consonantal", "stop", "dynamic", []⟩],
    actSlots := ["a", "t"], consSlots := ["a", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Or", .subject, .step, some "succ", "next-syllable|same=|delta=syll:1|min=", (1 : Int), some "consonantal", "stop", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Or", .subject, .step, some "succ", "next-syllable|same=|delta=syll:1|min=", (1 : Int), some "consonantal", "stop", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false }]

def total100 : String → Bool := fun s => ["Or"].contains s
def set100 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"c", "Or", .subject, .step, some "succ", "morph|same=morph|delta=|min=", (1 : Int), some "consonantal", "stop", "dynamic", []⟩],
    actSlots := ["c", "t"], consSlots := ["c", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p", "Or", .trigger, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "consonantal", "stop", "dynamic", []⟩,
      ⟨"pp", "Or", .trigger, .stepof, some "succ", "unscoped", (-1 : Int), some "nuclear", "stop", "dynamic", []⟩,
      ⟨"n", "Or", .trigger, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "consonantal", "stop", "dynamic", []⟩,
      ⟨"nn", "Or", .trigger, .stepof, some "succ", "unscoped", (1 : Int), some "nuclear", "stop", "dynamic", []⟩],
    actSlots := ["n", "nn", "p", "pp", "t"], consSlots := ["t"], override := false }]

def total101 : String → Bool := fun s => ["Mel", "Or"].contains s
def set101 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p", "Or", .subject, .step, some "succ", "verb domain|same=vdom|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["p"], override := false },
  { slots := [⟨"t", "Mel", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Mel", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p", "Or", .trigger, .step, some "succ", "verb domain|same=vdom|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["p", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false }]

def total102 : String → Bool := fun s => ["Acc", "Or"].contains s
def set102 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Or", .trigger, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["h", "t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .trigger, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hn", "Or", .subject, .stepof, some "succ", "same morph|same=morph|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["hr", "t"], consSlots := ["h", "hn", "t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["h"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .trigger, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["h", "hr", "t"], consSlots := ["h", "t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hr", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["hr", "t"], override := false },
  { slots := [⟨"t", "Acc", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩,
      ⟨"p2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["p1", "p2", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Or", .trigger, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩,
      ⟨"n2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "nuclear", "skip", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n2"], override := false }]

def total103 : String → Bool := fun s => ["Or"].contains s
def set103 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Or", .subject, .search, some "succ", "word|same=word|delta=|min=", (1 : Int), some "round", "skip", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"c", "SCorr", .subject, .assoc, some "scorr", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["c", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false }]

def total104 : String → Bool := fun s => ["Or", "Tone"].contains s
def set104 : List Decl := [
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hn", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"hp", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"tn", "Tone", .subject, .step, some "tone_succ", "word|same=word|delta=|min=", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"tp", "Tone", .subject, .step, some "tone_succ", "word|same=word|delta=|min=", (-1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["h", "hn", "hp", "t", "tn", "tp"], consSlots := ["h", "hn", "hp", "t", "tn", "tp"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["h", "t"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false }]

def total105 : String → Bool := fun s => ["Or"].contains s
def set105 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Rel", .trigger, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), none, "stop", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p", "Rel", .trigger, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), none, "stop", "dynamic", []⟩],
    actSlots := ["p", "t"], consSlots := ["t"], override := false }]

def total106 : String → Bool := fun s => ["Or"].contains s
def set106 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"n", "Rel", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), none, "stop", "dynamic", []⟩],
    actSlots := ["n", "t"], consSlots := ["n"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"p", "Rel", .trigger, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), none, "stop", "dynamic", []⟩,
      ⟨"n2", "Rel", .trigger, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), none, "stop", "dynamic", []⟩],
    actSlots := ["n2", "p", "t"], consSlots := ["t"], override := false }]

def total107 : String → Bool := fun s => ["Mora", "Or", "Tone"].contains s
def set107 : List Decl := [
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["h", "t"], override := false },
  { slots := [⟨"t", "Mora", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["h"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["h"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["h"], override := false },
  { slots := [⟨"t", "Tone", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"h", "Or", .subject, .assoc, some "assoc", "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["h", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false }]

def total108 : String → Bool := fun s => ["Or"].contains s
def set108 : List Decl := [
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := ["t"], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩,
      ⟨"l1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"l2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (-1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r1", "Or", .subject, .step, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩,
      ⟨"r2", "Or", .subject, .stepof, some "succ", "word|same=word|delta=|min=", (1 : Int), some "present", "skip", "dynamic", []⟩],
    actSlots := ["l1", "t"], consSlots := ["l1", "t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false },
  { slots := [⟨"t", "Or", .subject, .anchor, none, "unscoped", (1 : Int), none, "skip", "dynamic", []⟩],
    actSlots := [], consSlots := ["t"], override := false }]

def registered : List ((String → Bool) × List Decl) := [(total0, set0), (total1, set1), (total2, set2), (total3, set3), (total4, set4), (total5, set5), (total6, set6), (total7, set7), (total8, set8), (total9, set9), (total10, set10), (total11, set11), (total12, set12), (total13, set13), (total14, set14), (total15, set15), (total16, set16), (total17, set17), (total18, set18), (total19, set19), (total20, set20), (total21, set21), (total22, set22), (total23, set23), (total24, set24), (total25, set25), (total26, set26), (total27, set27), (total28, set28), (total29, set29), (total30, set30), (total31, set31), (total32, set32), (total33, set33), (total34, set34), (total35, set35), (total36, set36), (total37, set37), (total38, set38), (total39, set39), (total40, set40), (total41, set41), (total42, set42), (total43, set43), (total44, set44), (total45, set45), (total46, set46), (total47, set47), (total48, set48), (total49, set49), (total50, set50), (total51, set51), (total52, set52), (total53, set53), (total54, set54), (total55, set55), (total56, set56), (total57, set57), (total58, set58), (total59, set59), (total60, set60), (total61, set61), (total62, set62), (total63, set63), (total64, set64), (total65, set65), (total66, set66), (total67, set67), (total68, set68), (total69, set69), (total70, set70), (total71, set71), (total72, set72), (total73, set73), (total74, set74), (total75, set75), (total76, set76), (total77, set77), (total78, set78), (total79, set79), (total80, set80), (total81, set81), (total82, set82), (total83, set83), (total84, set84), (total85, set85), (total86, set86), (total87, set87), (total88, set88), (total89, set89), (total90, set90), (total91, set91), (total92, set92), (total93, set93), (total94, set94), (total95, set95), (total96, set96), (total97, set97), (total98, set98), (total99, set99), (total100, set100), (total101, set101), (total102, set102), (total103, set103), (total104, set104), (total105, set105), (total106, set106), (total107, set107), (total108, set108)]

theorem set0_well_typed : set0.all (fun d => wellTyped total0 d) = true := by decide +kernel
theorem set1_well_typed : set1.all (fun d => wellTyped total1 d) = true := by decide +kernel
theorem set2_well_typed : set2.all (fun d => wellTyped total2 d) = true := by decide +kernel
theorem set3_well_typed : set3.all (fun d => wellTyped total3 d) = true := by decide +kernel
theorem set4_well_typed : set4.all (fun d => wellTyped total4 d) = true := by decide +kernel
theorem set5_well_typed : set5.all (fun d => wellTyped total5 d) = true := by decide +kernel
theorem set6_well_typed : set6.all (fun d => wellTyped total6 d) = true := by decide +kernel
theorem set7_well_typed : set7.all (fun d => wellTyped total7 d) = true := by decide +kernel
theorem set8_well_typed : set8.all (fun d => wellTyped total8 d) = true := by decide +kernel
theorem set9_well_typed : set9.all (fun d => wellTyped total9 d) = true := by decide +kernel
theorem set10_well_typed : set10.all (fun d => wellTyped total10 d) = true := by decide +kernel
theorem set11_well_typed : set11.all (fun d => wellTyped total11 d) = true := by decide +kernel
theorem set12_well_typed : set12.all (fun d => wellTyped total12 d) = true := by decide +kernel
theorem set13_well_typed : set13.all (fun d => wellTyped total13 d) = true := by decide +kernel
theorem set14_well_typed : set14.all (fun d => wellTyped total14 d) = true := by decide +kernel
theorem set15_well_typed : set15.all (fun d => wellTyped total15 d) = true := by decide +kernel
theorem set16_well_typed : set16.all (fun d => wellTyped total16 d) = true := by decide +kernel
theorem set17_well_typed : set17.all (fun d => wellTyped total17 d) = true := by decide +kernel
theorem set18_well_typed : set18.all (fun d => wellTyped total18 d) = true := by decide +kernel
theorem set19_well_typed : set19.all (fun d => wellTyped total19 d) = true := by decide +kernel
theorem set20_well_typed : set20.all (fun d => wellTyped total20 d) = true := by decide +kernel
theorem set21_well_typed : set21.all (fun d => wellTyped total21 d) = true := by decide +kernel
theorem set22_well_typed : set22.all (fun d => wellTyped total22 d) = true := by decide +kernel
theorem set23_well_typed : set23.all (fun d => wellTyped total23 d) = true := by decide +kernel
theorem set24_well_typed : set24.all (fun d => wellTyped total24 d) = true := by decide +kernel
theorem set25_well_typed : set25.all (fun d => wellTyped total25 d) = true := by decide +kernel
theorem set26_well_typed : set26.all (fun d => wellTyped total26 d) = true := by decide +kernel
theorem set27_well_typed : set27.all (fun d => wellTyped total27 d) = true := by decide +kernel
theorem set28_well_typed : set28.all (fun d => wellTyped total28 d) = true := by decide +kernel
theorem set29_well_typed : set29.all (fun d => wellTyped total29 d) = true := by decide +kernel
theorem set30_well_typed : set30.all (fun d => wellTyped total30 d) = true := by decide +kernel
theorem set31_well_typed : set31.all (fun d => wellTyped total31 d) = true := by decide +kernel
theorem set32_well_typed : set32.all (fun d => wellTyped total32 d) = true := by decide +kernel
theorem set33_well_typed : set33.all (fun d => wellTyped total33 d) = true := by decide +kernel
theorem set34_well_typed : set34.all (fun d => wellTyped total34 d) = true := by decide +kernel
theorem set35_well_typed : set35.all (fun d => wellTyped total35 d) = true := by decide +kernel
theorem set36_well_typed : set36.all (fun d => wellTyped total36 d) = true := by decide +kernel
theorem set37_well_typed : set37.all (fun d => wellTyped total37 d) = true := by decide +kernel
theorem set38_well_typed : set38.all (fun d => wellTyped total38 d) = true := by decide +kernel
theorem set39_well_typed : set39.all (fun d => wellTyped total39 d) = true := by decide +kernel
theorem set40_well_typed : set40.all (fun d => wellTyped total40 d) = true := by decide +kernel
theorem set41_well_typed : set41.all (fun d => wellTyped total41 d) = true := by decide +kernel
theorem set42_well_typed : set42.all (fun d => wellTyped total42 d) = true := by decide +kernel
theorem set43_well_typed : set43.all (fun d => wellTyped total43 d) = true := by decide +kernel
theorem set44_well_typed : set44.all (fun d => wellTyped total44 d) = true := by decide +kernel
theorem set45_well_typed : set45.all (fun d => wellTyped total45 d) = true := by decide +kernel
theorem set46_well_typed : set46.all (fun d => wellTyped total46 d) = true := by decide +kernel
theorem set47_well_typed : set47.all (fun d => wellTyped total47 d) = true := by decide +kernel
theorem set48_well_typed : set48.all (fun d => wellTyped total48 d) = true := by decide +kernel
theorem set49_well_typed : set49.all (fun d => wellTyped total49 d) = true := by decide +kernel
theorem set50_well_typed : set50.all (fun d => wellTyped total50 d) = true := by decide +kernel
theorem set51_well_typed : set51.all (fun d => wellTyped total51 d) = true := by decide +kernel
theorem set52_well_typed : set52.all (fun d => wellTyped total52 d) = true := by decide +kernel
theorem set53_well_typed : set53.all (fun d => wellTyped total53 d) = true := by decide +kernel
theorem set54_well_typed : set54.all (fun d => wellTyped total54 d) = true := by decide +kernel
theorem set55_well_typed : set55.all (fun d => wellTyped total55 d) = true := by decide +kernel
theorem set56_well_typed : set56.all (fun d => wellTyped total56 d) = true := by decide +kernel
theorem set57_well_typed : set57.all (fun d => wellTyped total57 d) = true := by decide +kernel
theorem set58_well_typed : set58.all (fun d => wellTyped total58 d) = true := by decide +kernel
theorem set59_well_typed : set59.all (fun d => wellTyped total59 d) = true := by decide +kernel
theorem set60_well_typed : set60.all (fun d => wellTyped total60 d) = true := by decide +kernel
theorem set61_well_typed : set61.all (fun d => wellTyped total61 d) = true := by decide +kernel
theorem set62_well_typed : set62.all (fun d => wellTyped total62 d) = true := by decide +kernel
theorem set63_well_typed : set63.all (fun d => wellTyped total63 d) = true := by decide +kernel
theorem set64_well_typed : set64.all (fun d => wellTyped total64 d) = true := by decide +kernel
theorem set65_well_typed : set65.all (fun d => wellTyped total65 d) = true := by decide +kernel
theorem set66_well_typed : set66.all (fun d => wellTyped total66 d) = true := by decide +kernel
theorem set67_well_typed : set67.all (fun d => wellTyped total67 d) = true := by decide +kernel
theorem set68_well_typed : set68.all (fun d => wellTyped total68 d) = true := by decide +kernel
theorem set69_well_typed : set69.all (fun d => wellTyped total69 d) = true := by decide +kernel
theorem set70_well_typed : set70.all (fun d => wellTyped total70 d) = true := by decide +kernel
theorem set71_well_typed : set71.all (fun d => wellTyped total71 d) = true := by decide +kernel
theorem set72_well_typed : set72.all (fun d => wellTyped total72 d) = true := by decide +kernel
theorem set73_well_typed : set73.all (fun d => wellTyped total73 d) = true := by decide +kernel
theorem set74_well_typed : set74.all (fun d => wellTyped total74 d) = true := by decide +kernel
theorem set75_well_typed : set75.all (fun d => wellTyped total75 d) = true := by decide +kernel
theorem set76_well_typed : set76.all (fun d => wellTyped total76 d) = true := by decide +kernel
theorem set77_well_typed : set77.all (fun d => wellTyped total77 d) = true := by decide +kernel
theorem set78_well_typed : set78.all (fun d => wellTyped total78 d) = true := by decide +kernel
theorem set79_well_typed : set79.all (fun d => wellTyped total79 d) = true := by decide +kernel
theorem set80_well_typed : set80.all (fun d => wellTyped total80 d) = true := by decide +kernel
theorem set81_well_typed : set81.all (fun d => wellTyped total81 d) = true := by decide +kernel
theorem set82_well_typed : set82.all (fun d => wellTyped total82 d) = true := by decide +kernel
theorem set83_well_typed : set83.all (fun d => wellTyped total83 d) = true := by decide +kernel
theorem set84_well_typed : set84.all (fun d => wellTyped total84 d) = true := by decide +kernel
theorem set85_well_typed : set85.all (fun d => wellTyped total85 d) = true := by decide +kernel
theorem set86_well_typed : set86.all (fun d => wellTyped total86 d) = true := by decide +kernel
theorem set87_well_typed : set87.all (fun d => wellTyped total87 d) = true := by decide +kernel
theorem set88_well_typed : set88.all (fun d => wellTyped total88 d) = true := by decide +kernel
theorem set89_well_typed : set89.all (fun d => wellTyped total89 d) = true := by decide +kernel
theorem set90_well_typed : set90.all (fun d => wellTyped total90 d) = true := by decide +kernel
theorem set91_well_typed : set91.all (fun d => wellTyped total91 d) = true := by decide +kernel
theorem set92_well_typed : set92.all (fun d => wellTyped total92 d) = true := by decide +kernel
theorem set93_well_typed : set93.all (fun d => wellTyped total93 d) = true := by decide +kernel
theorem set94_well_typed : set94.all (fun d => wellTyped total94 d) = true := by decide +kernel
theorem set95_well_typed : set95.all (fun d => wellTyped total95 d) = true := by decide +kernel
theorem set96_well_typed : set96.all (fun d => wellTyped total96 d) = true := by decide +kernel
theorem set97_well_typed : set97.all (fun d => wellTyped total97 d) = true := by decide +kernel
theorem set98_well_typed : set98.all (fun d => wellTyped total98 d) = true := by decide +kernel
theorem set99_well_typed : set99.all (fun d => wellTyped total99 d) = true := by decide +kernel
theorem set100_well_typed : set100.all (fun d => wellTyped total100 d) = true := by decide +kernel
theorem set101_well_typed : set101.all (fun d => wellTyped total101 d) = true := by decide +kernel
theorem set102_well_typed : set102.all (fun d => wellTyped total102 d) = true := by decide +kernel
theorem set103_well_typed : set103.all (fun d => wellTyped total103 d) = true := by decide +kernel
theorem set104_well_typed : set104.all (fun d => wellTyped total104 d) = true := by decide +kernel
theorem set105_well_typed : set105.all (fun d => wellTyped total105 d) = true := by decide +kernel
theorem set106_well_typed : set106.all (fun d => wellTyped total106 d) = true := by decide +kernel
theorem set107_well_typed : set107.all (fun d => wellTyped total107 d) = true := by decide +kernel
theorem set108_well_typed : set108.all (fun d => wellTyped total108 d) = true := by decide +kernel

theorem registered_sets : registered.length = 109 := rfl

theorem registered_declarations : (registered.map (fun p => p.2.length)).sum = 527 := by decide +kernel

theorem registered_well_typed : registered.all (fun p => p.2.all (fun d => wellTyped p.1 d)) = true := by
  simp only [registered, List.all_cons, List.all_nil, Bool.true_and, Bool.and_true, set0_well_typed, set1_well_typed, set2_well_typed, set3_well_typed, set4_well_typed, set5_well_typed, set6_well_typed, set7_well_typed, set8_well_typed, set9_well_typed, set10_well_typed, set11_well_typed, set12_well_typed, set13_well_typed, set14_well_typed, set15_well_typed, set16_well_typed, set17_well_typed, set18_well_typed, set19_well_typed, set20_well_typed, set21_well_typed, set22_well_typed, set23_well_typed, set24_well_typed, set25_well_typed, set26_well_typed, set27_well_typed, set28_well_typed, set29_well_typed, set30_well_typed, set31_well_typed, set32_well_typed, set33_well_typed, set34_well_typed, set35_well_typed, set36_well_typed, set37_well_typed, set38_well_typed, set39_well_typed, set40_well_typed, set41_well_typed, set42_well_typed, set43_well_typed, set44_well_typed, set45_well_typed, set46_well_typed, set47_well_typed, set48_well_typed, set49_well_typed, set50_well_typed, set51_well_typed, set52_well_typed, set53_well_typed, set54_well_typed, set55_well_typed, set56_well_typed, set57_well_typed, set58_well_typed, set59_well_typed, set60_well_typed, set61_well_typed, set62_well_typed, set63_well_typed, set64_well_typed, set65_well_typed, set66_well_typed, set67_well_typed, set68_well_typed, set69_well_typed, set70_well_typed, set71_well_typed, set72_well_typed, set73_well_typed, set74_well_typed, set75_well_typed, set76_well_typed, set77_well_typed, set78_well_typed, set79_well_typed, set80_well_typed, set81_well_typed, set82_well_typed, set83_well_typed, set84_well_typed, set85_well_typed, set86_well_typed, set87_well_typed, set88_well_typed, set89_well_typed, set90_well_typed, set91_well_typed, set92_well_typed, set93_well_typed, set94_well_typed, set95_well_typed, set96_well_typed, set97_well_typed, set98_well_typed, set99_well_typed, set100_well_typed, set101_well_typed, set102_well_typed, set103_well_typed, set104_well_typed, set105_well_typed, set106_well_typed, set107_well_typed, set108_well_typed]

end Registered
end PhonologicalRequirements
