from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, Made, NodeId, Not, Or_, Positional,
                   Present, RelDecl, Resolves, SameFeat, Scope, Sigma, Slot,
                   SortDecl, Struct, TRUE)

VOICED_OBS = ("b", "d", "g", "z", "v")
VOICELESS_OBS = ("p", "t", "k", "s", "f")
SONORANTS = ("m", "n", "l", "r", "w", "j")
VOWELS = ("a", "e", "i", "o", "u")


def _row(nuclear, son, obs, voice, aff=False, dorfric=False, palfric=False):
    return dict(present=True, nuclear=nuclear, son=son, obs=obs, voice=voice,
                aff=aff, dorfric=dorfric, palfric=palfric)


GAPPED = {
    "aff": (("č", "ǰ", "Č"), ("ţ", "ʣ", "Ţ")),
    "dorfric": (("x", "ɣ", "X"),),
    "palfric": (("ʃ", "ʒ", "Ʃ"),),
}
EXTRA_PAIRS = (("ʂ", "ʐ"),)


def features(mode: str = "binary"):
    if mode not in ("binary", "privative"):
        raise ValueError(mode)
    f = {}
    for s in VOICED_OBS:
        f[s] = _row(False, False, True, True)
    for s in VOICELESS_OBS:
        f[s] = _row(False, False, True, False if mode == "binary" else None)
    for s in SONORANTS:
        f[s] = _row(False, True, False, True if mode == "binary" else None)
    for s in VOWELS:
        f[s] = _row(True, True, False, True if mode == "binary" else None)
    for cls, triples in GAPPED.items():
        for vl, vd, un in triples:
            f[vl] = _row(False, False, True, False if mode == "binary" else None, **{cls: True})
            f[vd] = _row(False, False, True, True, **{cls: True})
            f[un] = _row(False, False, True, None, **{cls: True})
    for vl, vd in EXTRA_PAIRS:
        f[vl] = _row(False, False, True, False if mode == "binary" else None)
        f[vd] = _row(False, False, True, True)
    f[ABSENT] = dict(present=False, nuclear=None, son=None, obs=None, voice=None,
                     aff=None, dorfric=None, palfric=None)
    return f


ALPHABET = (ABSENT,) + VOICED_OBS + VOICELESS_OBS + SONORANTS + VOWELS


def sigma(mode: str = "binary") -> Sigma:
    return Sigma(
        sorts={"Or": SortDecl("Or", "total", tier="seg"),
               "Rel": SortDecl("Rel", "derived", tier="seg")},
        relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
        features=features(mode),
        default_features=dict(present=True, nuclear=False, son=False,
                              obs=False, voice=None, aff=False, dorfric=False,
                              palfric=False),
        domains=("syll", "word", "phrase"))


PHRASE = Scope(same=("phrase",), label="phrase")
WORD = Scope(same=("word",), label="word")
T = Slot("t", "Or", "subject", kind="anchor")
NXT_WORD = Slot("nx", "Or", "trigger", kind="step", relation="succ", scope=WORD,
                direction=+1, policy="dynamic")
NXT = Slot("nx", "Or", "trigger", kind="step", relation="succ", scope=PHRASE,
           direction=+1, policy="dynamic")
NXS = Slot("nx", "Or", "subject", kind="step", relation="succ", scope=PHRASE,
           direction=+1, policy="dynamic")
PVT = Slot("pv", "Or", "trigger", kind="step", relation="succ", scope=PHRASE,
           direction=-1, policy="dynamic")
NONOBS = Slot("v", "Or", "trigger", kind="search", relation="succ",
              scope=PHRASE, direction=+1, filter="nuclear")


def devoice(domain: str) -> Decl:
    return Decl(f"DEVOICE_{domain.upper()}", "Or", (T,),
                And((Feat("obs", "t", True),
                     Positional("last_live_of", "t", domain))),
                Not(Feat("voice", "t", True)), scope=PHRASE)


def cluster_devoice() -> Decl:
    return Decl("CLUSTER_DEVOICE", "Or", (T, NONOBS),
                And((Feat("obs", "t", True), Not(Resolves("v")))),
                Not(Feat("voice", "t", True)), scope=PHRASE)


def agree(value: bool | None) -> Decl:
    if value is None:
        return Decl("AGREE_BOTH", "Or", (T, NXS),
                    And((Feat("obs", "t", True), Resolves("nx"),
                         Feat("obs", "nx", True))),
                    SameFeat("voice", ("t", "current"), ("nx", "current")),
                    scope=PHRASE)
    name = "AGREE_PLUS" if value else "AGREE_MINUS"
    return Decl(name, "Or", (T, NXT),
                And((Feat("obs", "t", True), Resolves("nx"),
                     Feat("obs", "nx", True), Feat("voice", "nx", value))),
                Feat("voice", "t", value), scope=PHRASE)


def ident_voice() -> Decl:
    return Decl("ID_VOICE", "Or", (T,), Not(Made("t")),
                SameFeat("voice", ("t", "current"), ("t", "reference")),
                kind="faithfulness", locus_side="reference")


def ident_onset_voice() -> Decl:
    return Decl("ID_ONSET_VOICE", "Or", (T, NXT),
                And((Not(Made("t")), Feat("obs", "t", True), Resolves("nx"),
                     Feat("son", "nx", True))),
                SameFeat("voice", ("t", "current"), ("t", "reference")),
                kind="faithfulness", locus_side="reference", scope=PHRASE)


def no_voice() -> Decl:
    return Decl("NO_VOICE", "Or", (T,), Feat("obs", "t", True),
                Not(Feat("voice", "t", True)), scope=PHRASE)


def no_voiced(cls: str) -> Decl:
    return Decl(f"NO_VOICED_{cls.upper()}", "Or", (T,),
                And((Feat("obs", "t", True), Feat(cls, "t", True))),
                Not(Feat("voice", "t", True)), scope=PHRASE)


def ident_presonorant_voice() -> Decl:
    return Decl("ID_PRESON_VOICE", "Or", (T, NXT_WORD),
                And((Not(Made("t")), Feat("obs", "t", True), Resolves("nx"),
                     Feat("son", "nx", True))),
                SameFeat("voice", ("t", "current"), ("t", "reference")),
                kind="faithfulness", locus_side="reference", scope=PHRASE)


def gap_declarations(classes=()):
    ds = [ident_voice(), ident_presonorant_voice(), no_voice(), agree(None)]
    ds += [no_voiced(c) for c in classes]
    return {d.name: d for d in ds}


def declarations(devoicing=("syll",), assimilation="both",
                 cluster: bool = False):
    ds = [ident_voice(), ident_onset_voice()]
    for d in devoicing:
        ds.append(devoice(d))
    if cluster:
        ds.append(cluster_devoice())
    if assimilation == "both":
        ds.append(agree(None))
    elif assimilation == "plus":
        ds.append(agree(True))
    elif assimilation == "minus":
        ds.append(agree(False))
    elif assimilation == "plus_minus":
        ds += [agree(True), agree(False)]
    elif assimilation != "none":
        raise ValueError(assimilation)
    return {d.name: d for d in ds}


def struct(segments, sylls=None, words=None, phrase: int = 0):
    n = len(segments)
    if sylls is None:
        sylls = list(range(n))
    if words is None:
        words = [0] * n
    nodes, real, dom = [], {}, {}
    for i, v in enumerate(segments):
        nd = NodeId("Or", "lex", i)
        nodes.append(nd); real[nd] = v
        dom[nd] = {"syll": sylls[i], "word": words[i], "phrase": phrase}
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom)
