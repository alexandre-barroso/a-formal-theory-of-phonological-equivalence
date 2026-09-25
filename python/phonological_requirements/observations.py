from __future__ import annotations

LITHUANIAN = {
    "ap-gauti":    "abgauti",
    "ap-berti":    "apiberti",
    "at-taiki:ti": "atitaiki:ti",
}


ARAPAHO = {
    "TRIG1": (["é", "tʃ", "e", "s", "í", "i", "h", "i", "ʔ"], "ATTESTED"),
    "TRIG2": (["é", "tʃ", "e", "t", "i", "i"], "ATTESTED"),
    "TRIG3": (["n", "ó", "ó", "h", "o", "b", "é", "θ", "e", "n"], "ATTESTED"),
    "CLUS1": (["é", "tʃ", "e", "s", "n", "ó", "w", "o", "ʔ"], "ATTESTED"),
    "CLUS2": (["tʃ", "e", "b", "k", "ó", "ó", "h", "u"], "ATTESTED"),
    "CLUS3": (["n", "i", "h", "b", "e", "b", "í", "i", "s", "t", "i", "i", "t"],
           "ATTESTED"),
    "RND1": (["w", "ó", "x", "h", "o", "o", "x"], "ATTESTED"),
    "RND2": (["h", "o", "o", "w", "b", "é", "n"], "ATTESTED"),
    "MADE1": (["b", "e", "k", "\u2205", "n", "o"], "LOGICALLY_CONSTRUCTED"),
    "SUPP1": (["é", "tʃ", "e", "s", "\u2205", "n", "ó", "w", "o", "ʔ"], "ATTESTED"),
    "SUPP2": (["n", "é", "í", "tʃ", "\u2205"], "ATTESTED"),
    "SUPP3": (["b", "e", "s", "\u2205"], "ATTESTED"),
    "SUPP4": (["b", "e", "b", "í", "i", "s", "\u2205", "t", "i", "i"], "ATTESTED"),
    "SUPP5": (["tʃ", "e", "b", "\u2205", "k", "ó", "ó", "h", "u"], "ATTESTED"),
}


WETZELS_MASCARO_TABLE_10 = {
    ((), "none"): "az laz tas dad",
    ((), "plus"): "az laz taz dad",
    ((), "minus"): "az las tas dad",
    ((), "both"): "az las taz dad",
    (("word",), "none"): "az laz tas dat",
    (("word",), "both"): "az las taz dat",
    (("syll",), "none"): "as las tas dat",
    (("syll",), "both"): "as las taz dat",
}
WETZELS_MASCARO_IMPOSSIBLE = (
    "syllable-final devoicing without word-final devoicing, no assimilation",
    "syllable-final devoicing without word-final devoicing, with assimilation",
)


ARAPAHO_ACCENT = {
    "OWL_SG":  ("béé.θei", "ATTESTED"),
    "OWL_2":   ("he.béé.θei.bin", "ATTESTED"),
    "OWL_3":   ("he.béé.θei.bí.noo", "ATTESTED"),
    "CHIEF_SG": ("néé.cee", "ATTESTED"),
    "CHIEF_PL": ("nee.céé.noʔ", "ATTESTED"),
    "BULL_SG":  ("he.néé.cee", "ATTESTED"),
    "BULL_PL":  ("he.néé.cee.noʔ", "ATTESTED"),
    "SPRING_LOC": ("hoo.xe.bí.neʔ", "ATTESTED"),
    "PUTDOWN_3PL": ("cíí.ne.nóú.ʔu", "ATTESTED"),
    "BIGFISH": ("ee.beθ.nó.woʔ", "ATTESTED"),
    "FUT_WALK": ("heet.níí.si.seet", "ATTESTED"),
    "WALK_ALONG": ("ce.wí.see", "ATTESTED"),
    "HORSE": ("wóx.hoox", "ATTESTED"),
    "NECKLACE": ("né.wo.ʔéín", "ATTESTED"),
}


CBP_TABLEAUX = {
    "(29a) Moro imperfective vP": {
        "constraints": ["MAX", "INT", "*H", "AL-H,L", "DEP"],
        "weights": [9, 2, 1, 10, 1],
        "rows": [("tʃombəDa", [0, 0, 0, 1, 0], 10, 0, 0),
                 ("(tʃóm)bəDa", [0, 0, 1, 0, 1], 2, 1, 1),
                 ("tʃombə(Dá)", [0, 0, 1, 1, 1], 12, 0, 0)]},
    "(29b) Moro perfective vP": {
        "constraints": ["MAX", "INT", "*H", "AL-H,L", "DEP"],
        "weights": [9, 2, 1, 1, 9],
        "rows": [("tʃombə(Dó)", [0, 0, 1, 1, 0], 2, 1, 1),
                 ("(tʃóm)bə(Dó)", [0, 0, 2, 0, 1], 11, 0, 0),
                 ("(tʃómbə́Dó)", [0, 2, 1, 0, 1], 14, 0, 0),
                 ("tʃombəD-o", [1, 0, 0, 1, 0], 10, 0, 0)]},
    "(40) Hebrew noun": {
        "constraints": ["ω=σσ", "REALIZE", "FAITH"], "weights": [1, 9, 9],
        "rows": [("té.le.graf", [1, 0, 0], 1, 1, 1),
                 ("til.gref", [0, 0, 1], 9, 0, 0)]},
    "(41) Hebrew verb": {
        "constraints": ["ω=σσ", "REALIZEMORPH", "FAITH"], "weights": [10, 9, 1],
        "rows": [("té.le.graf", [1, 1, 0], 19, 0, 0),
                 ("tí.li.gref", [1, 0, 1], 11, 0, 0),
                 ("til.gref", [0, 0, 1], 1, 1, 1),
                 ("tel.graf", [0, 1, 1], 10, 0, 0)]},
    "(48b) Kuria CP": {
        "constraints": ["μ4", "H,R", "ID-T"], "weights": [9, 9, 1],
        "rows": [("toraroma eGetOOkE", [1, 0, 0], 9, 0, 0),
                 ("toraroma eGétÓÓkE", [0, 0, 1], 1, 1, 1)]},
    "(55) Guébie imperfective CP": {
        "constraints": ["*0", "PDROP", "ID-T(R,φ)", "ID-T"], "weights": [16, 23, 8, 8],
        "rows": [("e4 li3", [0, 1, 0, 0], 23, 0, 0),
                 ("e4 li2", [0, 0, 0, 1], 8, 1, 1),
                 ("e5 li3", [0, 0, 1, 1], 16, 0, 0),
                 ("e4 li1", [0, 0, 0, 2], 16, 0, 0),
                 ("e4 li0", [1, 0, 0, 3], 40, 0, 0)]},
    "(56) Guébie imperfective CP, low verb": {
        "constraints": ["*0", "PDROP", "ID-T(R,φ)", "ID-T"], "weights": [16, 23, 8, 8],
        "rows": [("e4 pa1", [0, 1, 0, 0], 23, 0, 0),
                 ("e4 pa0", [1, 0, 0, 1], 24, 0, 0),
                 ("e5 pa1", [0, 0, 1, 1], 16, 1, 1)]},
    "(63d) Tommo So Poss+N+Adj": {
        "constraints": ["HL-Rω", "L-Lω", "ID"], "weights": [16, 17, 8],
        "rows": [("ú bàbè mOnjú", [1, 0, 1], 24, 1, 1),
                 ("ú bàbé mOnjú", [1, 1, 0], 33, 0, 0),
                 ("ú bábè mOnjú", [0, 1, 2], 33, 0, 0),
                 ("ú bábé mOnjú", [1, 1, 1], 41, 0, 0),
                 ("ù bàbè mOnjú", [1, 0, 2], 32, 0, 0)]},
    "(64) Tommo So Poss only": {
        "constraints": ["HL-Rω", "L-Lω", "ID"], "weights": [16, 1, 8],
        "rows": [("ú bàbè", [1, 0, 1], 24, 0, 0),
                 ("ú bàbé", [1, 0, 0], 16, 0, 0),
                 ("ú bábè", [0, 0, 2], 16, 0, 0),
                 ("ú bábé", [0, 0, 1], 8, 1, 1)]},
    "(65) Tommo So Mod only": {
        "constraints": ["HL-Rω", "L-Lω", "ID"], "weights": [1, 17, 8],
        "rows": [("bàbè mOnjú", [0, 0, 1], 8, 1, 1),
                 ("bàbé mOnjú", [0, 1, 0], 17, 0, 0),
                 ("bábè mOnjú", [0, 1, 2], 33, 0, 0),
                 ("bábé mOnjú", [0, 1, 1], 25, 0, 0)]},
    "(66d) Jamsay Poss+N+Adj": {
        "constraints": ["HL-Rω", "L-Lφ", "ID"], "weights": [8, 16, 1],
        "rows": [("ù lèjù mOnú", [1, 0, 2], 10, 1, 1),
                 ("ú lèjù mOnú", [1, 1, 1], 25, 0, 0),
                 ("ú lèjú mOnú", [1, 1, 0], 24, 0, 0),
                 ("ú léjù mOnú", [0, 1, 2], 18, 0, 0)]},
    "(67d) Nanga Poss+N+Adj": {
        "constraints": ["HL-Rω", "L-Lφ", "ID"], "weights": [10, 9.5, 1],
        "rows": [("ú lésî mOsí", [0, 1, 1], 10.5, .6, .62),
                 ("ù lèsì mOsí", [1, 0, 1], 11, .4, .38),
                 ("ú lèsí mOsí", [1, 1, 0], 19.5, 0, 0),
                 ("ú lèsì mOsí", [1, 1, 1], 20.5, 0, 0)]},
}

CBP_WINNERS = {
    "MORO_IPFV_VP": "(tʃóm)bəDa",
    "MORO_PFV_VP": "tʃombə(Dó)",
    "MORO_IPFV_CP": "ga(tʃóm)bəDa",
    "TOMMO_SO": ["ú bàbè mOnjú"],
    "JAMSAY": ["ù lèjù mOnú"],
    "NANGA": ["ú lésî mOsí", "ù lèsì mOsí"],
}


ANTTILA_FINNISH = {
 "kala":        ("ká.lo.jen", "ká.loi.den", 100.0, 0.0, 500, 0, "a"),
 "lasi":        ("lá.si.en", "lá.sei.den", 100.0, 0.0, 500, 0, "i"),
 "kamera":      ("ká.me.ro.jen", "ká.me.ròi.den", 0.0, 100.0, 0, 720, "a"),
 "hetero":      ("hé.te.ro.jen", "hé.te.ròi.den", 0.5, 99.5, 2, 89, "o"),
 "naapuri":     ("náa.pu.ri.en", "náa.pu.rèi.den", 63.1, 36.9, 368, 215, "i"),
 "maailma":     ("máa.il.mo.jen", "máa.il.mòi.den", 49.5, 50.5, 45, 46, "a"),
 "korjaamo":    ("kór.jaa.mo.jen", "kór.jaa.mòi.den", 82.2, 17.8, 350, 76, "o"),
 "poliisi":     ("pó.lii.si.en", "pó.lii.sèi.den", 98.4, 1.6, 806, 13, "i"),
 "taiteilija":  ("tái.tei.li.jo.jen", "tái.tei.li.jòi.den", 0.0, 100.0, 0, 276, "a"),
 "luettelo":    ("lú.et.te.lo.jen", "lú.et.te.lòi.den", 0.0, 100.0, 0, 25, "o"),
 "ministeri":   ("mí.nis.te.ri.en", "mí.nis.te.rèi.den", 85.7, 14.3, 234, 39, "i"),
 "luonnehdinta":("lúon.neh.dìn.to.jen", "lúon.neh.dìn.noi.den", 100.0, 0.0, 1, 0, "a"),
 "edustusto":   ("é.dus.tùs.to.jen", "é.dus.tùs.toi.den", 100.0, 0.0, 84, 0, "o"),
 "margariini":  ("már.ga.rìi.ni.en", "már.ga.rìi.nei.den", 100.0, 0.0, 736, 0, "i"),
 "ajattelija":  ("á.jat.te.li.jo.jen", "á.jat.te.li.jòi.den", 0.0, 100.0, 0, 101, "a"),
 "televisio":   ("té.le.vi.si.o.jen", "té.le.vi.si.òi.den", 0.0, 100.0, 0, 41, "o"),
 "Aleksanteri": ("á.lek.sàn.te.ri.en", "á.lek.sàn.te.rèi.den", 88.2, 11.8, 15, 2, "i"),
 "evankelista": ("é.van.ke.lìs.to.jen", "é.van.ke.lìs.toi.den", 100.0, 0.0, 2, 0, "a"),
 "italiaano":   ("í.ta.li.àa.no.jen", "í.ta.li.àa.noi.den", 100.0, 0.0, 1, 0, "o"),
 "sosialisti":  ("só.si.a.lìs.ti.en", "só.si.a.lìs.tei.den", 100.0, 0.0, 99, 0, "i"),
 "koordinaatisto": ("kóor.di.nàa.tis.to.jen", "kóor.di.nàa.tis.tòi.den", 80.0, 20.0, 8, 2, "o"),
 "avantgardisti": ("á.vant.gàr.dis.ti.en", "á.vant.gàr.dis.tèi.den", 100.0, 0.0, 2, 0, "i"),
}
ANTTILA_PRINTED = {
 "kala": (100, 100), "lasi": (100, 100), "kamera": (0, 0.52), "hetero": (0, 0.57),
 "naapuri": (67, 69.51), "maailma": (50, 42.03), "korjaamo": (80, 81.61),
 "poliisi": (100, 100), "taiteilija": (0, 0.52), "luettelo": (0, 0.56),
 "ministeri": (67, 69.49), "luonnehdinta": (100, 100), "edustusto": (100, 100),
 "margariini": (100, 100), "ajattelija": (0, 0.52), "televisio": (0, 0.57),
 "Aleksanteri": (67, 69.51), "evankelista": (100, 100), "italiaano": (100, 100),
 "sosialisti": (100, 100), "koordinaatisto": (80, 81.61), "avantgardisti": (100, 100),
}
ANTTILA_TD_PATTERNS = {1: ("cost.V", "cost.C"), 4: ("cos.tV", "cost.C"),
                       5: ("cos.tV", "cos.tC"), 6: ("cos.tV", "cos.C"), 9: ("cos.V", "cos.C")}
ANTTILA_TD_COUNTS = {"V": {"cos.tV": 70, "cost.V": 25, "cos.V": 25},
                     "C": {"cos.tC": 20, "cost.C": 50, "cos.C": 50}}


GOUSKOVA_21 = {
    "kot":  ("kot-am",  "kot",  "kod ʐe",  "kot to"),
    "kod":  ("kod-am",  "kot",  "kod ʐe",  "kot to"),
    "bok":  ("bok-am",  "bok",  "bog ʐe",  "bok to"),
    "bog":  ("bog-am",  "bok",  "bog ʐe",  "bok to"),
    "noč":  ("noč-am",  "noč",  "noǰ ʐe",  "noč to"),
    "ţex":  ("ţex-am",  "ţex",  "ţeɣ ʐe",  "ţex to"),
    "veʃ":  ("veʃ-am",  "veʃ",  "veʒ ʐe",  "veʃ to"),
    "lʐeţ": ("lʐeţ-am", "lʐeţ", "lʐeʣ ʐe", "lʐeţ to"),
}
GOUSKOVA_OTHER = {
    "mozg bi": "mozg bi", "mozg": "mosk", "vosk bi": "vozg bi", "mozg to": "mosk to",
    "mozg li": "mosk li", "ob-man": "obman", "tigr": "tigr", "bok": "bok", "kod": "kot",
    "kot bi": "kod bi", "noč bi": "noǰ bi", "mox bi": "moɣ bi",
    "imidʐ": "imitʂ", "imidʐ-a": "imidʐa", "imidʐ bi": "imidʐ bi",
    "k vsem": "k fsem",
}
GOUSKOVA_18_INPUTS = ("bat", "pad", "adpat", "atbat")
GOUSKOVA_18 = {
    "a": ((("Agree", "Id-pson"), ("*ObsVoice",), ("Ident",)), ("bat", "pat", "atpat", "adbat")),
    "b": ((("Agree", "Id-pson"), ("Ident",), ("*ObsVoice",)), ("bat", "pad", "atpat", "adbat")),
    "c": ((("Id-pson",), ("*ObsVoice",), ("Agree", "Ident")), ("bat", "pat", "atpat", "atbat")),
    "d": ((("Ident", "Id-pson"), ("*ObsVoice", "Agree")), ("bat", "pad", "adpat", "atbat")),
    "e": ((("*ObsVoice", "Agree"), ("Ident", "Id-pson")), ("pat", "pat", "atpat", "atpat")),
    "f": ((("Agree",), ("Ident",), ("*ObsVoice",), ("Id-pson",)), ("bat", "pad", "atpat", "atpat")),
}
GOUSKOVA_18_SYSTEMS_STATED = 7


LIKO = {
    "(12a)": ("i? a? a? a?", "I a a a"),
    "(12b)": ("i? a? a? a?", "I a a a"),
    "(12c)": ("u? a?", "U a"),
    "(12d)": ("i? i? o?", "I I O"),
    "(12e)": ("i a? a?", "i o o"),
    "(12f)": ("u a? a? a?", "u o o o"),
    "(12g)": ("u a? i?", "u o i"),
    "(12h)": ("i i? o?", "i i o"),
    "(13a)": ("i i? U", "i i U"),
    "(13b)": ("u i? O", "u i O"),
    "(13c)": ("i i? a? a? i? U", "i i o o i U"),
    "(13d)": ("i o o? u U", "i o o u U"),
    "(13e)": ("i a? i? I", "i o i I"),
    "(13f)": ("a? u O", "o u O"),
    "(14a)": ("i a? O", "i a O"),
    "(14b)": ("i a? U", "i a U"),
    "(14c)": ("i i? a? I", "i i a I"),
    "(14d)": ("i a? a? U", "i a a U"),
    "(14e)": ("o a? a? U", "o a a U"),
    "(15c)": ("o u o?", "o u o"),
    "(15d)": ("i a? i? o? U", "i o i O U"),
}
YAKA = {
    "(9a)": (("i", "i a"), "i a"),
    "(9b)": (("e", "i i a"), "i i a"),
    "(9c)": (("e", "i"), "i"),
    "(9d)": (("e", "i i"), "i i"),
    "(10a)": (("e", "i e"), "e e"),
    "(10b)": (("e", "i i i e"), "e e e e"),
    "(10c)": (("o", "i i e"), "e e e"),
    "(11a)": (("i", "i e"), "i i"),
    "(11b)": (("i", "i i e"), "i i i"),
    "(11c)": (("a", "i i e"), "i i i"),
}
TUTRUGBU_TAFI = {
    "(5a)": (("U U", "u"), "u u"), "(5b)": (("a a", "u"), "e e"),
    "(5c)": (("a I", "u"), "e i"), "(5d)": (("a I a", "u"), "e i e"),
    "(6a)": (("U U", "i"), "u u"), "(6b)": (("a a", "i"), "e e"),
    "(6c)": (("a I", "u"), "e i"), "(6d)": (("a I a", "i"), "e i e"),
    "(7a)": (("I a", "u"), "I a"), "(7b)": (("I a", "e"), "I a"),
    "(7c)": (("I I a", "u"), "I I a"), "(7d)": (("I I a a", "u"), "I I a a"),
    "(7e)": (("I I a a a", "u"), "I I a a a"), "(7f)": (("I a I", "u"), "I a i"),
    "(8a)": (("U a", "i"), "U a"), "(8b)": (("I a", "i"), "I a"),
    "(8c)": (("I I a", "i"), "I I a"), "(8d)": (("I I a", "u"), "I I a"),
}
TAFI_TABLE_3 = {("high", "all_high"): (19, 20), ("high", "some_nonhigh"): (0, 7),
                ("nonhigh", "all_high"): (28, 28), ("nonhigh", "some_nonhigh"): (113, 115)}
LIKO_TABLE_6 = {"=INS≐NEG": (0, 29), "-FV≐NEG": (0, 10), "-FV≐SUPP": (0, 3), "-FV≐P.3": (5, 38)}
YAKA_ILE_COUNTS = {"-ele": 453, "-ene": 378, "-idi": 419, "-ini": 103}


ANTIGEM = {
    "afar": [("xaməl-i", "xaml-i"), ("ʔagər-i", "ʔagr-i"), ("darəg-u", "darg-u"),
             ("digəb-e", "digb-e"), ("wagər-e", "wagr-e"), ("meʔər-a", "meʔr-a"),
             ("midədi", "midədi"), ("sabəba", "sabəba"), ("xarər-e", "xarər-e"),
             ("gonən-a", "gonən-a"), ("adəd-e", "adəd-e"), ("danən-e", "danən-e"),
             ("modəd-e", "modəd-e"),
             ("as-əs-e-y-yo", "as-s-e-y-yo"), ("xas-əs-e-y-yo", "xas-s-e-y-yo"), ("sas-əs-e-tto", "sas-s-e-tto")],
    "tonkawa": [("notəxo", "notxo"), ("picəna", "picna"), ("hewəwa", "hewəwa"), ("haṃəṃa", "haṃəṃa"),
                ("yakəpa", "yakpa"), ("yakəkəpa", "yakəkpa")],
    "tiberian": [("zaaXərúu", "zaaXrúu"), ("saabəbúu", "saabəbúu"), ("yaaðəʕúu", "yaaðʕúu"), ("daaləlúu", "daaləlúu"),
                 ("ʔaaxəláa", "ʔaaxláa"), ("naasəsáa", "naasəsáa"), ("haaləxúu", "haalxúu"), ("saaləlúu", "saaləlúu"),
                 ("tə-βaarex-əxaa", "tə-βaarex-xaa")],
    "modern_hebrew": [("kasər-u", "kasr-u"), ("nadəd-u", "nadəd-u"), ("kusər-a", "kusr-a"), ("kucəc-a", "kucəc-a"),
                      ("hitkaʃər-u", "hitkaʃr-u"), ("titpaləl-i", "titpaləl-i")],
    "iraqi": [("saʔər-ak", "saʔr-ak"), ("xaabər-at", "xaabr-at"), ("yḥaddəd-uun", "yḥaddəd-uun"),
              ("mʔaθθəθ-a", "mʔaθθəθ-a"), ("haajəj-at", "haajəj-at"), ("mḥaadəd-a", "mḥaadəd-a")],
    "damascene": [("btaskən-i", "btaskn-i"), ("bisaaʕəd-u", "bisaaʕd-u"), ("bisabbəb-u", "bisabbəb-u"),
                  ("taxassəs-ak", "taxassəs-ak"), ("biḥaazəz-u", "biḥaazəz-u"),
                  ("madd-ət-o", "madd-ət-o"), ("ḥaṭṭ-ət-o", "ḥaṭṭ-ət-o"), ("fəḍḍ-ət-o", "fəḍḍ-ət-o")],
    "yupik": [("kəmə-ni", "kəm-ni"), ("qatəgak", "qatgak"), ("avəga", "avga"),
              ("atə-tə-q", "atə-tə-q"), ("kəmə-mi", "kəmə-mi")],
    "chevak": [("anə=ni", "an=ni"), ("kəmə-mi", "kəmə-mi"), ("atə=tə-q", "at=tə-q")],
    "akkadian": [("daməqat", "damqat"), ("lemənu", "lemnu"), ("rapəsum", "rapsum"),
                 ("dubəbii", "dubbii"), ("sakəkat", "sakkat"), ("issaləlu", "issallu")],
}


GCS_TABLE_1 = {"V_final_contexts": 131, "V_final_apocope": 80, "V_final_incomplete": 31,
               "C_final_contexts": 61, "C_final_apocope": 22, "C_final_incomplete": 9,
               "C_deletion": 56}
GCS_VARIANTS = {"A": ("pás", "pás"), "B": ("pásos", "páso"), "C": ("páso", "páso"),
                "D": ("pásos", "pás"), "E": ("páso", "pás")}
GCS_TABLE_6 = {"V_final": {"páso": 39, "pás": 61},
               "C_final": {"pásos": 8, "páso": 56, "pás": 36}}
GCS_WORDS = {"paso": ("p á s o", "p á s o s"), "paxaro": ("p á x a ɾ o", "p á x a ɾ o s"),
             "metro": ("m é t ɾ o", "m é t ɾ o s"), "oferta": ("o f é ɾ t a", "o f é ɾ t a s")}
GCS_TABLE_15 = {"V_final": {"páso": 41, "pás": 57, "other": 2}, "C_final": {"pásos": 12, "páso": 52, "pás": 32, "other": 4}}
GCS_TABLE_15_SOURCE_NOTE = "Printed p. 44 reports mean 32 with interval 33–34 for C-final apocope. The inconsistency is preserved; the mean is not silently replaced by an interval endpoint."
GCS_TABLE_18 = {"V_final": {"páso": 38, "pás": 61, "other": 1}, "C_final": {"pásos": 13, "páso": 57, "pás": 29, "other": 1}}
GCS_TABLE_18_BY_GROUP = {
    "paso_metro": GCS_TABLE_18,
    "paxaro_oferta": {"V_final": {"páso": 38, "pás": 55, "other": 7},
                      "C_final": {"pásos": 13, "páso": 56, "pás": 24, "other": 7}},
}
GCS_TABLE_8 = {"noSM": {"MAE": 19.1}, "1SM": {"MAE": 8.2, "LL": -6.567}, "2SM": {"MAE": 3.4, "LL": -6.505},
               "parallel_OT_contextual": {"MAE": 4.1, "LL": -6.676}}
GCS_APPENDIX_2 = {"VD1": 0.36, "CD": 0.92, "VD2": 0.39}


KAZAKH = {"alma": ("alma.lar", "alma.ma", "alma.ga"), "mandaj": ("mandaj.lar", "mandaj.ma", "mandaj.ga"),
          "kijar": ("kijar.lar", "kijar.ma", "kijar.ga"), "kol": ("kol.dar", "kol.ma", "kol.ga"),
          "murin": ("murin.dar", "murin.ba", "murin.ga"), "koŋɯz": ("koŋɯz.dar", "koŋɯz.ba", "koŋɯz.ga"),
          "syjek": ("syjek.ter", "syjek.pe", "syjek.ke")}
KIRGHIZ = {"too": ("too.lar", "too.nu"), "aj": ("aj.dar", "aj.dɯ"), "kar": ("kar.dar", "kar.dɯ"),
           "rol": ("rol.dar", "rol.du"), "atan": ("atan.dar", "atan.dɯ"), "taʃ": ("taʃ.tar", "taʃ.tɯ"),
           "konok": ("konok.tar", "konok.tu")}
KIRGHIZ_59 = {"koldo-ba": "koldo.ba", "ber-ba": "ber.be", "ʒaz-ba": "ʒaz.ba", "ket-ba": "ket.pe"}
SIDAMO = {"maʕ-toti": "maʕ.toti", "ful-te": "ful.te", "qaram-tino": "qaran.tino",
          "duk-nanni": "duŋ.kanni", "huʔ-nanni": "hun.ʔanni", "has-nemmo": "han.semmo", "hab-nemmo": "ham.bemmo",
          "af-tinonni": "af.finonni", "lelliʃ-toti": "lelliʃ.ʃoti", "ful-nemmo": "ful.lemmo", "um-nommo": "um.mommo",
          "hab-toti": "hab.boti", "ag-tu": "ag.gu", "amad-tino": "amad.dino", "mar-nonni": "mar.ronni"}
FAROESE = [("a:.ʰkwamarin", 7, "onset"), ("vea:.ʰkrir", 6, "onset"), ("ai:.ʰtranti", 6, "onset"), ("ðea:.ʰprir", 6, "onset"),
           ("mi:.ʰklir", 5, "onset"), ("e:.ʰpli", 5, "onset"),
           ("sig.ri", 4, "coda"), ("baʰt.na", 4, "coda"), ("ig.la", 3, "coda"), ("ves.na", 3, "coda"),
           ("ðar.na", 2, "coda"), ("roʰk.ti", 0, "coda"), ("ves.tyr", -1, "coda"), ("hen.dyr", -2, "coda"),
           ("ðœr.di", -4, "coda"), ("styʰt.lijyr", 5, "coda tl"), ("lyʰt.li", 5, "coda tl")]
ICELANDIC = [("bið.ja", 4, "coda"), ("stœð.wa", 4, "coda"), ("hœɣ.ri", 3, "coda"), ("blað.ra", 3, "coda"),
             ("sig.la", 3, "coda"), ("vis.na", 3, "coda"), ("tem.ja", 3, "coda"), ("vel.ja", 2, "coda"),
             ("ver.ja", 1, "coda"), ("tew.ja", 0, "coda"), ("hes.tyr", -1, "coda"), ("ew.ri", -1, "coda"),
             ("aw.laga", -2, "coda"), ("ðwer.gyr", -4, "coda"),
             ("vi:.tja", 7, "onset"), ("vœ:.kwa", 7, "onset"), ("a:.krar", 6, "onset"), ("ti:.tra", 6, "onset"),
             ("sko:.pra", 6, "onset"), ("twi:.swar", 6, "onset"), ("e:.sja", 6, "onset"),
             ("eʰp.li", 5, "coda"), ("eʰk.la", 5, "coda"), ("œʰt.la", 5, "coda")]
GOUSKOVA_TABLE_II = {"Icelandic": "+5", "Faroese": "+4", "Kazakh": "-1", "Sidamo": "-2", "Kirghiz": "-3 or lower"}

ALDERETE_JP = {
    "hasi_1": ("hási", "(3.33)"), "hasi_2": ("hasí", "(3.33)"), "hasi_0": ("hasi", "(3.33)"),
    "inoti": ("ínoti", "(3.35)"), "kokoro": ("kokóro", "(3.35)"), "atama": ("atamá", "(3.35)"),
    "miyako": ("miyako", "(3.35)"),
    "yom_tara": ("yóm-tara", "(5.10b)"), "yob_tara": ("yob-tára", "(5.10b)"),
    "abura_ppo": ("abura-ppó-i", "(5.8a)"), "ada_ppo": ("ada-ppó-i", "(5.8b)"),
    "kiza_ppo": ("kiza-ppó-i", "(5.8b)"),
    "edo_kko": ("edo-kko", "(5.9a)"), "koobe_kko": ("koobe-kko", "(5.9b)"),
    "nyuuyooku_kko": ("nyuuyooku-kko", "(5.9b)"),
    "yosida_ke": ("yosidá-ke", "(5.77a)"), "nisimura_ke": ("nisimurá-ke", "(5.77b)"),
    "andoo_ke": ("andóo-ke", "(5.77b)"),
    "yosida_si": ("yosidá-si", "(5.81a)"), "nisimura_si": ("nisímura-si", "(5.81b)"),
    "satoo_si": ("sátoo-si", "(5.81b)"),
    "ma_futatu": ("ma-fútatu", "(5.72a)"), "ma_yonaka": ("ma-yónaka", "(5.72a)"),
    "kaki_mono": ("kakí-mono", "(5.114a)"), "yomi_mono": ("yomí-mono", "(5.114a)"),
    "nori_mono": ("nori-mono", "(5.114b)"), "wasure_mono": ("wasure-mono", "(5.114b)"),
    "kuzu_ya": ("kuzú-ya", "(5.115a)"), "kona_ya": ("koná-ya", "(5.115a)"),
    "toma_ya": ("toma-ya", "(5.115b)"),
    "kaki_te": ("kaki-té", "(5.116a)"), "katari_te": ("katari-te", "(5.116b)"),
    "inoti_nagara": ("inoti-nágara", "§5.4.3"), "miyako_nagara": ("miyako-nagara", "§5.4.3"),
    "kawa_no": ("kawa-no", "(5.41a)"), "atama_no": ("atama-no", "(5.41a)"),
    "umi_no": ("úmi-no", "(5.41b)"), "utiwa_no": ("utíwa-no", "(5.41b)"),
    "ehon_no": ("ehóN-no", "(5.41c): /ehóN + no/ → ehón no; N the moraic nasal"),
    "hon_no": ("hóN-no", "(5.41d): /hón + no/ → hón no"), "hukoo_no": ("hukóo-no", "(5.41c)"),
    "ha_no": ("há-no", "(5.41d)"), "kyoo_no": ("kyóo-no", "(5.41d)"),
}

ALDERETE_RU = {
    "rak_u": ("rák-u", "(3.11)"), "rak_ami": ("rák-ami", "(3.11)"), "rak_i_acc": ("rák-i", "(3.17)"),
    "stol_u": ("stol-ú", "(3.12)"), "stol_ami": ("stol-ámi", "(3.20b)"), "stol_i_acc": ("stol-í", "(3.23b')"),
    "topor_0": ("topór", "(3.21)"), "topor_u": ("topor-ú", "(3.21)"),
    "komnat_i": ("kómnat-i", "(3.19a)"), "tetrad_i": ("tetrád-i", "(3.19b)"),
    "luz_ic_a": ("lúž-ic-a", "(5.21a)"), "cast_ic_a": ("čast-íc-a", "(5.21b)"),
    "siv_ux_a": ("siv-úx-a", "(5.23a)"), "skak_ux_a": ("skak-úx-a", "(5.23b)"),
    "puz_ac_u": ("puz-ač-ú", "(5.24a)"), "izb_ac_u": ("izb-ač-ú", "(5.24b)"),
    "borod_ac_u": ("borod-ač-ú", "(5.24c)"),
    "rukav_a": ("rukav-á", "(5.25)"), "master_a": ("master-á", "(5.25)"), "promysl_i": ("prómɨsl-i", "§5.2.3, paragraph after (5.25): prómysl-i, y = ɨ"),
    "kolokol_u": ("kólokol-u", "(5.35a)"), "kolokol_am": ("kolokol-ám", "(5.35a)"),
    "kolbas_e": ("kolbas-é", "(5.35b)"), "kolbas_am": ("kolbás-am", "(5.35b)"),
    "vi_pisat": ("ví-p'isa-t'", "(3.30): p'isát' → ví-p'isat'; analysed as a dominant prefix in §5.2.3"),
}

ALDERETE_CU = {
    "pe_yax": ("pé-yax", "(2.24a)"), "ne_yax": ("né-yax", "(2.24a)"),
    "pe_yax_qal": ("pe-yax-qál", "(2.24b)"), "yax_qal_i": ("yax-qal-í", "(2.27)"),
    "ne_wen_qal": ("ne-wen-qál", "(2.26b)"), "yax_em": ("yáx-em", "(2.28a)"), "max_em": ("máx-em", "(2.28b)"),
    "mi_ne_tew": ("mi-né-tew", "(2.29a)"),
    "pe_miaw_lu": ("pe-míʔaw-lu", "(2.30a)"), "ayu_qa": ("ʔáyu-qa", "(2.30b)"),
    "pe_tul_qa": ("pe-túl-qa", "(2.31)"), "pe_pulin_qal": ("pe-pulín-qal", "(2.31)"),
    "ne_ngiy_qal_i_pe": ("ne-ŋíy-qal-i-pe", "(2.31)"),
    "wena_nuk": ("wená-nuk", "§2.4.3, paragraph before (2.40); (5.61a)"), "ne_ma_ci": ("ne-má-či", "(2.40)"),
    "pe_tama_nga": ("pe-tamá-ŋa", "(2.42)"), "meme_yke": ("méme-yke", "(2.43a)"),
    "tivie_maa_le": ("tíviʔe-maa-le", "(2.43b)"),
    "yax_i_qa_te": ("yax-í-qa-te", "(2.48a)"), "kwa_i_qa_te": ("kwa-í-qa-te", "(2.48b)"),
    "pacike_i_ce": ("páčike-i-če", "(2.47)"), "wiwe_i_ce": ("wíwe-i-če", "(2.47)"),
    "ne_max_i_ve_ngax": ("ne-max-í-ve-ŋax", "(2.48c)"),
}


NUER = {
    "A1": ([("b", "LH"), ("b", "H"), "+"], {"LH-H", "M-H"}, "Table 6 #__-H, breathy"),
    "A2": ([("m", "LH"), ("b", "H"), "+"], {"LH-H", "M-H"}, "Table 6 #__-H, modal"),
    "A3": ([("b", "LH"), ("m", "H"), "+"], {"LH-HL"}, "Table 6 #__-HL, breathy; Fig 11"),
    "A4": ([("m", "LH"), ("m", "H"), "+"], {"LH-HL"}, "Table 6 #__-HL, modal; §5.4 'realized only as LH-HL'"),
    "A5": ([("b", "LH"), ("b", "L"), "+"], {"LH-L", "M-L"}, "Table 6 #__-L, breathy"),
    "A6": ([("m", "LH"), ("b", "L"), "+"], {"LH-L", "M-L", "HL-L"}, "Table 6 #__-L, modal"),
    "A7": ([("b", "LH"), ("b", "LH"), "+"], {"LH-M", "M-M"}, "Table 6 #__-M; §5.4 (6) LH-LH -> LH-M, first optionally M"),
    "A8": ([("b", "LH"), ("m", "LH"), "+"], {"LH-M", "M-M", "LH-HL"}, "§5.4: LH-HL if the second syllable is modal"),
    "A9": ([("m", "LH"), ("b", "LH"), "+"], {"LH-M", "M-M"}, "§5.4"),
    "A10": ([("m", "LH"), ("m", "LH"), "+"], {"LH-M", "M-M", "LH-HL"}, "§5.4"),
    "B1": ([("b", "H"), ("b", "LH")], {"H-L"}, "Table 6 H-__#; Fig 16a-i"),
    "B2": ([("m", "H"), ("b", "LH")], {"HL-L"}, "Table 6 HL-__#; Fig 16a-ii"),
    "B3": ([("b", "H"), ("m", "LH")], {"H-L"}, "Table 6 H-__#, modal"),
    "B4": ([("m", "H"), ("m", "LH")], {"HL-L"}, "Table 6 HL-__#, modal"),
    "B5": ([("b", "L"), ("b", "LH")], {"L-L", "L-M"}, "Table 6 L-__#; Fig 16b"),
    "B6": ([("b", "L"), ("m", "LH")], {"L-L", "L-M"}, "Table 6 L-__#, modal"),
    "B7": ([("b", "LH"), ("b", "LH")], {"LH-M", "M-M"}, "Table 6 LH-__# and M-__#, breathy; Fig 16c-i"),
    "B8": ([("b", "LH"), ("m", "LH")], {"LH-M", "M-M", "LH-HL"}, "Table 6 LH-__#, modal: {M, HL}"),
    "C1": ([("b", "L"), ("m", "LH"), ("b", "L"), "+"], {"L-HL-L", "L-M-L"}, "Figs 12b, 13b; §5.2 (4)"),
    "C2": ([("b", "L"), ("b", "LH"), ("b", "L"), "+"], {"L-M-L"}, "§5.2: 'if the second syllable contains a breathy vowel, only the mid allotone'"),
    "C3": ([("b", "LH"), ("m", "LH"), ("b", "L"), "+"], {"LH-HL-L", "LH-M-L", "M-M-L"}, "Figs 12a, 13a; §5.4"),
    "E1": ([("b", "L"), ("m", "LH"), ("b", "LH")], {"L-HL-L", "L-M-M"}, "Fig 16c-ii (HL then L) and 16c-i type (M then M)"),
    "D1": ([("b", "H"), "+"], {"H"}, "§4: high level on breathy vowels"),
    "D2": ([("m", "H"), "+"], {"HL"}, "§4: falling on modal vowels"),
    "D3": ([("b", "L"), "+"], {"L"}, "§3, §6: the Low toneme has no allotones"),
    "D4": ([("m", "H"), ("m", "H"), "+"], {"HL-HL"}, "§5.4: 'two High tonemes over modal vowels are realized as HL-HL'"),
    "D5": ([("b", "H"), ("b", "L")], {"H-L"}, "Fig 2a type: high then low, phrase-final low"),
    "D6": ([("b", "LH"), "+"], {"LH", "M"}, "§5.1: rising and mid in free variation (Fig 9)"),
}


NEZ = {
    "K1": ([("hekiN", 0, 0), ("én’i", 0, 1, ("app2",)), ("see", 0, 1)], {"heknéy’se"}, "(70a) hexnéy’se; (25a)"),
    "K2": ([("hekiN", 0, 0), ("én’i", 0, 1, ("app2",)), ("see", 0, 1), ("m", 1, 1), ("qa", 1, 1)], {"heknéy’semqa"}, "(70b) haxnáy’sàmqa; (25b), (30c)"),
    "K3": ([("hekiN", 0, 0), ("én’i", 0, 1, ("app2",)), ("", 0, 1), ("m", 1, 1), ("e", 1, 1)], {"heknén’ime"}, "(70c) hexnénìme; (71b)"),
    "K4": ([("kuu", 0, 0, ("alt",)), ("én’i", 0, 1, ("app2",)), ("uu’", 0, 1)], {"kiyén’yu’", "kiyén’u’"}, "(19a) kiyén’yu’ (the applicative's final vowel before a vowel: glide or deletion not compared)"),
    "K5": ([("hipi", 0, 0), ("én’i", 0, 1, ("app2",)), ("t", 0, 1)], {"hipén’it"}, "(20a) hipén’it"),
    "K6": ([("pée", 0, 2), ("kuu", 0, 0, ("alt",)), ("én’i", 0, 1, ("app2",)), ("", 0, 1), ("qaane", 1, 1)], {"péekiyen’iqane"}, "(29a) páakiyan’iqana with -qaane a fused word-level tense (§3.2); (48ix)"),
    "K7": ([("’e", 0, 2), ("’iyáaqN", 0, 0), ("én’i", 0, 1, ("app2",)), ("qaa", 0, 1), ("qa", 1, 1)], {"’e’yáaqney’qaqa"}, "(30d) ’aw’yáaẋnay’qaqa"),
    "K8": ([("hekiN", 0, 0), ("én’i", 0, 1, ("app2",)), ("", 0, 1), ("m", 1, 1)], {"heknén’im"}, "(20e) hexné’nim (glottal shift undone)"),
    "K9": ([("nées", 0, 2), ("kuu", 0, 0, ("alt",)), ("én’i", 0, 1, ("app2",)), ("", 0, 1), ("m", 1, 1), ("e", 1, 1)], {"néeskiyen’ime"}, "(12b) nées-kiy-en’i-m-e; (48viii)"),
    "K10": ([("pée", 0, 2), ("kuu", 0, 0, ("alt",)), ("én’i", 0, 1, ("app2",)), ("", 0, 1), ("e", 1, 1)], {"péekiyen’ye", "péekiyen’e"}, "(19c) péekiyen’ye (the final vowel before a vowel not compared)"),
    "K11": ([("pée", 0, 2), ("kuu", 0, 0, ("alt",)), ("én’i", 0, 1, ("app2",)), ("see", 0, 1)], {"péekiyey’se"}, "(21a) péekiyey’se"),
    "K13": ([("’e", 0, 2), ("’iyáqN", 0, 0), ("én’i", 0, 1, ("app2",)), ("", 0, 1), ("m", 1, 1), ("e", 1, 1)], {"’e’yáqnen’ime"}, "(22c) ’aw’-yáẋn-an’i-m-a (the root's length as printed there)"),
    "R1": ([("hi", 0, 2), ("kuu", 0, 0, ("alt",)), ("", 0, 1), ("e", 1, 1)], {"hikúye", "hikúuye"}, "(13a) hi-kú(u)y-e"),
    "R2": ([("kuu", 0, 0, ("alt",)), ("siix", 0, 1)], {"kusíix"}, "(11b) ku-siix"),
    "R3": ([("kuu", 0, 0, ("alt",)), ("táayN", 0, 1), ("see", 0, 1)], {"kutáayce"}, "(14a) kotáayca"),
    "S1": ([("nikée", 0, 2), ("hawaq", 0, 0), ("see", 0, 1)], {"nikéehwaqse"}, "(52a) ni.káah.waq.sa"),
    "S2": ([("tukwéep", 0, 2), ("hawaq", 0, 0), ("see", 0, 1)], {"tukwéephawqse"}, "(52b) to.káap.hawq.sa"),
    "S3": ([("páa", 0, 2), ("t’awáanii", 0, 0), ("see", 0, 1)], {"páat’wanise"}, "(57c) páat’.wa.ni.sa"),
    "S4": ([("hi", 0, 2), ("t’awáanii", 0, 0), ("uu’", 0, 1)], {"hit’wáaniyu’"}, "(57b) hit’.wáa.ni.yo’"),
    "S5": ([("hi", 0, 2), ("tuk’wéep", 0, 2), ("t’awáanii", 0, 0), ("qaane", 1, 1)], {"hitk’wéept’awaniqane"}, "(57d) hit.k’óop.t’a.wa.ni.qa.na"),
    "S6": ([("hekiN", 0, 0), ("see", 0, 1)], {"hekíce"}, "(23a) hekíce"),
    "S7": ([("hi", 0, 2), ("cúukweN", 0, 0), ("sii", 0, 1), ("ne", 1, 1)], {"hicúukwecine"}, "(32b) hicúukwecine; (48ii)"),
    "S8": ([("hipi", 0, 0), ("see", 0, 1), ("ne", 1, 1)], {"hipséene"}, "p. 419 hipséene"),
    "S10": ([("hi", 0, 2), ("túxii", 0, 0), ("siix", 0, 1)], {"hitúxisix"}, "(54a) hi.tú.xi-six"),
    "S11": ([("hi", 0, 2), ("wíi", 0, 2), ("túxii", 0, 0), ("siix", 0, 1)], {"hiwíituxisix"}, "(54b) hi.wíi.tu.xi-six"),
    "S12": ([("pée", 0, 2), ("heewtuk’íi", 0, 0), ("", 0, 1), ("e", 1, 1)], {"péehewtuk’iye"}, "(55a) pée.hew.tu.k’i.ye"),
    "S13": ([("heewtuk’íi", 0, 0), ("see", 0, 1)], {"hewtuk’íise"}, "(55b) hew.tu.k’íi.se"),
    "N1": ([("hi", 0, 2), ("q’uuyímN", 0, 0), ("", 0, 1), ("e", 1, 1)], {"hiq’uyímne"}, "fn 11 hiq’uyímne (the root's first vowel long, as fn 11's q’uuyímN-úu-see)"),
    "N2": ([("hi", 0, 2), ("q’uuyímN", 0, 0), ("see", 0, 1)], {"hiq’uyímce"}, "fn 11 hiq’uyímce"),
    "N3": ([("q’uuyímN", 0, 0), ("űu", 0, 1), ("see", 0, 1)], {"q’uyimnúuse"}, "fn 11 q’uyimnúuse (the directional suffix dominant, (40))"),
    "T3": ([("wáawaa", 0, 0), ("e̋et", 0, 1)], {"wawayéet"}, "(48iii) wàa.wa.yáat (the agent suffix dominant, (42))"),
    "T4": ([("hi", 0, 2), ("nées", 0, 2), ("cúukweN", 0, 0), ("see", 0, 1)], {"hinéescukwece"}, "(48iv) hìnèescùkwèce; (33a)"),
    "T5": ([("hi", 0, 2), ("nées", 0, 2), ("páayN", 0, 0), ("űu", 0, 1), ("see", 0, 1)], {"hinespaynúuse"}, "(48v) hìnàspàynóosa; (40b)"),
}

NEZ_RESIDUE = {
    "X1": ([("hi", 0, 2), ("pe", 0, 2), ("kuu", 0, 0, ("alt",)), ("", 0, 1), ("e", 1, 1)], {"hipekúye"}, "(48i) hìpekúye: the prefix vowel is not syncopated"),
    "X2": ([("hi", 0, 2), ("nées", 0, 2), ("hite̋emeeN", 0, 0), ("", 0, 1), ("e", 1, 1)], {"hineshitéemene"}, "(42c) hinesitéemene: the root-initial vowel is not syncopated (derived by the cluster ban reading the lexical length of the preceding nucleus)"),
    "X3": ([("sepée", 0, 2), ("hite̋emeeN", 0, 0), ("ew’e̋et", 0, 1)], {"sepehitemenew’éet"}, "(48vii) sèpèhìtèmenèw’éet, (43a): the same root-initial vowel; the root's second vowel long as in (43b)"),
}


SANDHI = {
    "experiment_1": {"feeding": "S11", "second": "T1", "third": "T1",
                     "table": {"T2T3T1": {"T2T3T1": 259},
                               "T3T3T1": {"T3T3T1": 7, "T2T3T1": 242},
                               "T2T1T1": {"T2T1T1": 74, "T2T3T1": 167},
                               "T3T1T1": {"T3T1T1": 59, "T3T3T1": 46, "T2T3T1": 131}},
                     "observed_rates": {"underlying": 0.972, "derived": 0.740},
                     "locator": "Table 2, p. 573; rates p. 572; 11 speakers"},
    "experiment_2": {"feeding": "S44", "second": "T4", "third": "T4",
                     "table": {"T2T3T4": {"T2T3T4": 386},
                               "T3T3T4": {"T3T3T4": 20, "T2T3T4": 368},
                               "T2T4T4": {"T2T4T4": 156, "T2T3T4": 212},
                               "T3T4T4": {"T3T4T4": 98, "T3T3T4": 213, "T2T3T4": 68}},
                     "observed_rates": {"underlying": 0.948, "derived": 0.242},
                     "locator": "Table 5, p. 579; rates p. 578; 20 speakers (five from experiment 1)"},
}

SCHWA = {
    "n": 162,
    "proportions": {1: 0.090, 2: 0.122, 3: 0.683, 4: 0.833, 5: 0.562, 6: 0.648, 7: 0.914, 8: 0.938},
    "counts": {1: 15, 2: 20, 3: 111, 4: 135, 5: 91, 6: 105, 7: 148, 8: 152},
    "wilson_95": {1: (0.05, 0.14), 2: (0.08, 0.18), 3: (0.61, 0.75), 4: (0.76, 0.89), 5: (0.48, 0.64), 6: (0.57, 0.72), 7: (0.86, 0.95), 8: (0.89, 0.97)},
    "labels": {1: "/0/, C, -ss (epenthetic, C_, before two syllables)", 2: "/0/, C, -s", 3: "/0/, CC, -ss", 4: "/0/, CC, -s",
               5: "/@/, C, -ss (underlying, clitic te)", 6: "/@/, C, -s", 7: "/@/, CC, -ss", 8: "/@/, CC, -s"},
    "note": "Smith & Pater 2020 Table 14 p. 24 (three decimals; the values used for their fits were more precise); Table 3 p. 14 gives two decimals with Wilson 95% intervals; Flemming 2021 Table 2 p. 23 repeats the two-decimal values; n = 27 x 6 = 162 per context assumed complete",
    "locator": "smithPater2020frenchSchwa: (23) p. 11, (25) p. 12, (27) p. 13, (28) p. 13, Table 3 p. 14, Table 14 p. 24, (36) p. 24; flemming2021comparing: (19) p. 13, (24)-(28) pp. 14-15, (35) p. 18, Table 2 p. 23",
}
