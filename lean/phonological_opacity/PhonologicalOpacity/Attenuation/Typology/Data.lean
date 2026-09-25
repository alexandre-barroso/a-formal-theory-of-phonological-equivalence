import PhonologicalOpacity.Attenuation.Typology.Core
namespace InteractionTypology
def pattern0 : Pattern := {
alphabet := [("k",["C"]),("V",["V"]),("N",["C","N"]),("T",["C","T"])]
rules := [⟨"NDEL","N",[],["#"],none⟩,⟨"TDEL","T",["N"],["#"],none⟩]
faith := [⟨"MAX_N","N",none⟩,⟨"MAX_T","T",none⟩]
names := ["MAX_N","MAX_T","NDEL","TDEL"]
options := [("N",[(some "N"),none]),("T",[(some "T"),none])]
observations := [(["k","V","N"],"kV"),(["k","V","N","T"],"kVN"),(["k","V","N","V"],"kVNV")] }
def pattern1 : Pattern := {
alphabet := [("k",["C"]),("V",["V"]),("N",["C","N"]),("T",["C","T"])]
rules := [⟨"NDEL","N",[],["#"],none⟩,⟨"TDEL","T",["N"],["#"],none⟩]
faith := [⟨"MAX_N","N",none⟩,⟨"MAX_T","T",none⟩]
names := ["MAX_N","MAX_T","NDEL","TDEL"]
options := [("N",[(some "N"),none]),("T",[(some "T"),none])]
observations := [(["k","V","N"],"kV"),(["k","V","N","T"],"kV"),(["k","V","N","V"],"kVNV")] }
def pattern2 : Pattern := {
alphabet := [("k",["C","k"]),("kj",["C"]),("i",["V","i"]),("I",["V"]),("m",["C"]),("t",["C"]),("n",["C"]),("a",["V"])]
rules := [⟨"PAL","k",[],["i"],(some "kj")⟩,⟨"SYNC","i",[],["C","V"],none⟩]
faith := [⟨"IDENT_k_kj","k",(some "kj")⟩,⟨"MAX_i","i",none⟩]
names := ["IDENT_k_kj","MAX_i","PAL","SYNC"]
options := [("k",[(some "k"),(some "kj")]),("i",[(some "i"),none])]
observations := [(["k","i","m"],"kjim"),(["t","i","m","I","n"],"tmIn"),(["k","i","m","I","n"],"kjmIn")] }
def pattern3 : Pattern := {
alphabet := [("k",["C","k"]),("kj",["C"]),("i",["V","i"]),("I",["V"]),("m",["C"]),("t",["C"]),("n",["C"]),("a",["V"])]
rules := [⟨"PAL","k",[],["i"],(some "kj")⟩,⟨"SYNC","i",[],["C","V"],none⟩]
faith := [⟨"IDENT_k_kj","k",(some "kj")⟩,⟨"MAX_i","i",none⟩]
names := ["IDENT_k_kj","MAX_i","PAL","SYNC"]
options := [("k",[(some "k"),(some "kj")]),("i",[(some "i"),none])]
observations := [(["k","i","m"],"kjim"),(["t","i","m","I","n"],"tmIn"),(["k","i","m","I","n"],"kmIn")] }
def pattern4 : Pattern := {
alphabet := [("g",["C"]),("a",["V"]),("h",["C","h"]),("w",["C","w"]),("u",["V"]),("t",["C"]),("d",["C"]),("r",["C"]),("e",["V"]),("m",["C"])]
rules := [⟨"HDEL","h",[],["C"],none⟩,⟨"VOC","w",["C"],["#"],(some "u")⟩]
faith := [⟨"IDENT_w_u","w",(some "u")⟩,⟨"MAX_h","h",none⟩]
names := ["HDEL","IDENT_w_u","MAX_h","VOC"]
options := [("h",[(some "h"),none]),("w",[(some "w"),(some "u")])]
observations := [(["g","a","h","t"],"gat"),(["d","a","r","w"],"daru"),(["m","a","w"],"maw"),(["g","a","h","e"],"gahe"),(["g","a","h","w"],"gau")] }
def pattern5 : Pattern := {
alphabet := [("g",["C"]),("a",["V"]),("h",["C","h"]),("w",["C","w"]),("u",["V"]),("t",["C"]),("d",["C"]),("r",["C"]),("e",["V"]),("m",["C"])]
rules := [⟨"HDEL","h",[],["C"],none⟩,⟨"VOC","w",["C"],["#"],(some "u")⟩]
faith := [⟨"IDENT_w_u","w",(some "u")⟩,⟨"MAX_h","h",none⟩]
names := ["HDEL","IDENT_w_u","MAX_h","VOC"]
options := [("h",[(some "h"),none]),("w",[(some "w"),(some "u")])]
observations := [(["g","a","h","t"],"gat"),(["d","a","r","w"],"daru"),(["m","a","w"],"maw"),(["g","a","h","e"],"gahe"),(["g","a","h","w"],"gaw")] }
def pattern6 : Pattern := {
alphabet := [("g",["C"]),("a",["V"]),("h",["C","h"]),("w",["C","w"]),("u",["V"]),("t",["C"]),("d",["C"]),("r",["C"]),("e",["V"]),("m",["C"])]
rules := [⟨"HDEL","h",[],["C"],none⟩,⟨"VOC","w",["C"],["#"],(some "u")⟩]
faith := [⟨"IDENT_w_u","w",(some "u")⟩,⟨"MAX_h","h",none⟩]
names := ["HDEL","IDENT_w_u","MAX_h","VOC"]
options := [("h",[(some "h"),none]),("w",[(some "w"),(some "u")])]
observations := [(["g","a","h","t"],"gat"),(["d","a","r","w"],"daru"),(["m","a","w"],"maw"),(["g","a","h","e"],"gahe"),(["g","a","h","w"],"gahu")] }
def pattern7 : Pattern := {
alphabet := [("g",["C"]),("a",["V"]),("h",["C","h"]),("r",["C"]),("@",["@","V"]),("m",["C"]),("u",["V"]),("p",["C"]),("e",["V"]),("t",["C"])]
rules := [⟨"HDEL","h",[],["C"],none⟩,⟨"SYNC","@",["C","V"],["C","V"],none⟩]
faith := [⟨"MAX_@","@",none⟩,⟨"MAX_h","h",none⟩]
names := ["HDEL","MAX_@","MAX_h","SYNC"]
options := [("h",[(some "h"),none]),("@",[(some "@"),none])]
observations := [(["g","a","h","e"],"gahe"),(["g","a","h","t"],"gat"),(["m","a","e"],"mae"),(["m","a","t"],"mat"),(["m","a","r","@","m","u"],"marmu"),(["a","h","@","p","t"],"ah@pt"),(["a","h","@","p","r","@","m","u"],"ah@pr@mu"),(["g","a","h","r","@","m","u"],"gar@mu"),(["a","h","@","p","e"],"ahpe")] }
def pattern8 : Pattern := {
alphabet := [("C",["C","L"]),("V",["V"]),("K",["C","K"])]
rules := [⟨"APO","V",["C","V"],["#"],none⟩,⟨"KDEL","K",[],["#"],none⟩]
faith := [⟨"MAX_K","K",none⟩,⟨"MAX_V","V",none⟩]
names := ["APO","KDEL","MAX_K","MAX_V"]
options := [("V",[(some "V"),none]),("K",[(some "K"),none])]
observations := [(["C","V","C","V","C","V"],"CVCVC"),(["C","V","C","V","K"],"CVCV"),(["C","V","C","V","K","V"],"CVCV")] }
def pattern9 : Pattern := {
alphabet := [("C",["C"]),("V",["V"])]
rules := [⟨"CDEL","C",[],["#"],none⟩,⟨"VDEL","V",[],["#"],none⟩]
faith := [⟨"MAX_C","C",none⟩,⟨"MAX_V","V",none⟩]
names := ["CDEL","MAX_C","MAX_V","VDEL"]
options := [("C",[(some "C"),none]),("V",[(some "V"),none])]
observations := [(["C","V","C"],"CV"),(["C","V","C","V"],"CVC")] }
def pattern10 : Pattern := {
alphabet := [("V",["V"]),("C",["C"]),("@",["@","V"])]
rules := [⟨"SYNC","@",["C","V"],["C","V"],none⟩]
faith := [⟨"MAX_@","@",none⟩]
names := ["MAX_@","SYNC"]
options := [("@",[(some "@"),none])]
observations := [(["V","C","@","C","@","C","V"],"VCCCV")] }
def pattern11 : Pattern := {
alphabet := [("V",["V"]),("C",["C"]),("@",["@","V"])]
rules := [⟨"SYNC","@",["C","V"],["C","V"],none⟩]
faith := [⟨"MAX_@","@",none⟩]
names := ["MAX_@","SYNC"]
options := [("@",[(some "@"),none])]
observations := [(["V","C","@","C","@","C","V"],"VCC@CV")] }
def pattern12 : Pattern := {
alphabet := [("V",["V"]),("C",["C"]),("@",["@","V"])]
rules := [⟨"SYNC","@",["C","V"],["C","V"],none⟩]
faith := [⟨"MAX_@","@",none⟩]
names := ["MAX_@","SYNC"]
options := [("@",[(some "@"),none])]
observations := [(["V","C","@","C","@","C","V"],"VC@CCV")] }
def pattern13 : Pattern := {
alphabet := [("u",["V","rd"]),("y",["V","y"])]
rules := [⟨"RND","y",["rd"],[],(some "u")⟩]
faith := [⟨"IDENT_y_u","y",(some "u")⟩]
names := ["IDENT_y_u","RND"]
options := [("y",[(some "y"),(some "u")])]
observations := [(["u","y","y"],"uuy")] }
def pattern14 : Pattern := {
alphabet := [("u",["V","rd"]),("y",["V","y"])]
rules := [⟨"RND","y",["rd"],[],(some "u")⟩]
faith := [⟨"IDENT_y_u","y",(some "u")⟩]
names := ["IDENT_y_u","RND"]
options := [("y",[(some "y"),(some "u")])]
observations := [(["u","y","y"],"uuu")] }
def pattern15 : Pattern := {
alphabet := [("p",["C"]),("L",["L","V"]),("s",["C"]),("v",["C"]),("a",["V"])]
rules := [⟨"SHORT","L",["C","L"],[],(some "a")⟩]
faith := [⟨"IDENT_L_a","L",(some "a")⟩]
names := ["IDENT_L_a","SHORT"]
options := [("L",[(some "L"),(some "a")])]
observations := [(["p","L","s","L","v","L"],"pLsava")] }
def pattern16 : Pattern := {
alphabet := [("p",["C"]),("L",["L","V"]),("s",["C"]),("v",["C"]),("a",["V"])]
rules := [⟨"SHORT","L",["C","L"],[],(some "a")⟩]
faith := [⟨"IDENT_L_a","L",(some "a")⟩]
names := ["IDENT_L_a","SHORT"]
options := [("L",[(some "L"),(some "a")])]
observations := [(["p","L","s","L","v","L"],"pLsavL")] }
def pattern17 : Pattern := {
alphabet := [("X",["C","X"]),("Y",["C","Y"]),("A",["A","V"]),("B",["B","V"]),("Q",["Q","V"])]
rules := [⟨"AB","A",["X"],["Y"],(some "B")⟩,⟨"BQ","B",["X"],["Y"],(some "Q")⟩,⟨"QA","Q",["X"],["Y"],(some "A")⟩]
faith := [⟨"IDENT_A_B","A",(some "B")⟩,⟨"IDENT_A_Q","A",(some "Q")⟩,⟨"IDENT_B_A","B",(some "A")⟩,⟨"IDENT_B_Q","B",(some "Q")⟩,⟨"IDENT_Q_A","Q",(some "A")⟩,⟨"IDENT_Q_B","Q",(some "B")⟩]
names := ["AB","BQ","IDENT_A_B","IDENT_A_Q","IDENT_B_A","IDENT_B_Q","IDENT_Q_A","IDENT_Q_B","QA"]
options := [("A",[(some "A"),(some "B"),(some "Q")]),("B",[(some "A"),(some "B"),(some "Q")]),("Q",[(some "A"),(some "B"),(some "Q")])]
observations := [(["X","A","Y"],"XBY"),(["X","B","Y"],"XQY"),(["X","Q","Y"],"XAY")] }
def pattern18 : Pattern := {
alphabet := [("i",["V","i"]),("k",["C","k"]),("kj",["C"]),("ts",["C"]),("a",["V"])]
rules := [⟨"PAL","k",[],["i"],(some "kj")⟩,⟨"AFF","k",["i"],[],(some "ts")⟩]
faith := [⟨"IDENT_k_kj","k",(some "kj")⟩,⟨"IDENT_k_ts","k",(some "ts")⟩]
names := ["AFF","IDENT_k_kj","IDENT_k_ts","PAL"]
options := [("k",[(some "k"),(some "kj"),(some "ts")])]
observations := [(["a","k","i"],"akji"),(["i","k","a"],"itsa"),(["i","k","i"],"iki")] }
def pattern19 : Pattern := {
alphabet := [("i",["V","i"]),("k",["C","k"]),("kj",["C"]),("ts",["C"]),("a",["V"])]
rules := [⟨"PAL","k",[],["i"],(some "kj")⟩,⟨"AFF","k",["i"],[],(some "ts")⟩]
faith := [⟨"IDENT_k_kj","k",(some "kj")⟩,⟨"IDENT_k_ts","k",(some "ts")⟩]
names := ["AFF","IDENT_k_kj","IDENT_k_ts","PAL"]
options := [("k",[(some "k"),(some "kj"),(some "ts")])]
observations := [(["a","k","i"],"akji"),(["i","k","a"],"itsa"),(["i","k","i"],"ikji")] }
def pattern20 : Pattern := {
alphabet := [("M",["M","V"]),("R",["R","V"]),("H",["V"]),("L",["V"])]
rules := [⟨"MR","M",[],["R"],(some "L")⟩,⟨"RM","R",[],["M"],(some "H")⟩]
faith := [⟨"IDENT_M_L","M",(some "L")⟩,⟨"IDENT_R_H","R",(some "H")⟩]
names := ["IDENT_M_L","IDENT_R_H","MR","RM"]
options := [("M",[(some "M"),(some "L")]),("R",[(some "R"),(some "H")])]
observations := [(["M","R"],"LR"),(["R","M"],"HM"),(["M","R","M"],"LHM"),(["R","M","R"],"HLR")] }
instance : Inhabited Pattern := ⟨pattern0⟩
def patterns : List Pattern := [pattern0,pattern1,pattern2,pattern3,pattern4,pattern5,pattern6,pattern7,pattern8,pattern9,pattern10,pattern11,pattern12,pattern13,pattern14,pattern15,pattern16,pattern17,pattern18,pattern19,pattern20]
def system0 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(0,0),(-1,0),(0,-1),(1,0)],[(1,0),(-1,0),(0,-1),(0,0)],[(1,0),(0,0),(0,-1),(0,0)],[(1,0),(0,0),(0,0),(0,0)]]]
def system1 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(0,0),(-1,0),(0,-1),(1,0)],[(1,0),(-1,0),(0,-1),(1,0)],[(1,0),(0,0),(0,-1),(0,0)],[(1,0),(0,0),(0,0),(0,0)]]]
def system2 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(-1,0),(0,0),(1,0)],[(-1,0),(0,0),(0,1),(0,0)],[(0,0),(-1,0),(0,0),(0,0)],[(1,0),(0,0),(0,0),(0,0)]]]
def system3 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(-1,0),(0,0),(1,0)],[(-1,0),(0,0),(0,1),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)]]]
def system4 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(0,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(-1,0),(0,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)]]]
def system5 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(1,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(-1,0),(0,0),(1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)]]]
def system6 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(0,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(-1,0),(1,0),(1,0)],[(1,0),(-1,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)]]]
def system7 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(1,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(-1,0),(0,0),(1,0)],[(1,0),(-1,0),(-1,0),(1,0)],[(1,0),(0,0),(-1,0),(0,0)]]]
def system8 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(1,0),(-1,0),(-1,0),(1,0)],[(0,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(0,0)]]]
def system9 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(1,0),(-1,0),(-1,0),(1,0)],[(0,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)]]]
def system10 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(1,0),(-1,0),(-1,0),(1,0)],[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(0,0)]]]
def system11 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(1,0),(-1,0),(-1,0),(1,0)],[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)]]]
def system12 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(1,0),(0,0),(-1,0),(1,0)],[(0,0),(1,0),(-1,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)]]]
def system13 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(1,0),(-1,0),(-1,0)],[(0,0),(1,0),(0,0),(-1,0)]]]
def system14 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(1,0),(0,0),(-1,0),(1,0)],[(1,0),(1,0),(-1,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)]]]
def system15 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(1,0),(0,0),(-1,0),(0,0)],[(1,0),(1,0),(-1,0),(-1,0)],[(0,0),(1,0),(0,0),(-1,0)]]]
def system16 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(1,0),(-1,0),(0,0),(1,0)],[(0,0),(-1,0),(1,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)]]]
def system17 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(1,0),(-1,0),(0,0),(1,0)],[(0,0),(-1,0),(1,0),(1,0)],[(0,0),(0,0),(1,0),(0,0)]]]
def system18 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(-1,0),(-1,0),(1,0),(0,0)],[(-1,0),(0,0),(1,0),(0,0)]]]
def system19 : List (List Delta) := [[[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(-1,0),(0,0),(1,0),(0,0)]]]
def system20 : List (List Delta) := [[[(0,0),(0,0),(1,0),(0,0)],[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,1),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(0,0),(1,0),(1,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,1),(1,0),(0,0),(0,0)],[(0,1),(2,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(0,0),(1,0),(1,0),(0,0)],[(0,0),(1,0),(1,0),(0,0)],[(0,0),(2,0),(1,0),(0,0)],[(1,0),(0,0),(-1,0),(0,-1)],[(1,0),(1,0),(-1,0),(0,-1)],[(0,0),(1,0),(0,0),(0,-1)],[(0,-1),(-1,0),(0,0),(1,0)],[(0,-1),(-1,0),(1,0),(0,0)],[(0,-1),(0,0),(1,0),(0,0)]]]
def system21 : List (List Delta) := [[[(0,0),(0,0),(1,0),(0,0)],[(1,0),(0,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,1),(1,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(0,0),(1,0),(1,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,1),(1,0),(0,0),(0,0)],[(0,1),(2,0),(0,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(0,0),(1,0),(1,0),(0,0)],[(0,0),(1,0),(1,0),(0,0)],[(0,0),(2,0),(1,0),(0,0)],[(1,0),(0,0),(-1,0),(0,-1)],[(1,0),(1,0),(-1,0),(0,-1)],[(0,0),(1,0),(0,0),(0,-1)],[(0,-1),(-1,0),(0,0),(1,0)],[(0,-1),(-1,0),(1,0),(1,0)],[(0,-1),(0,0),(1,0),(0,0)]]]
def system22 : List (List Delta) := [[[(1,0),(0,0),(0,0),(-1,0)],[(0,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(2,0)],[(0,-1),(1,0),(-1,0),(0,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(2,0)],[(0,-1),(0,0),(0,0),(2,0)],[(1,-1),(0,0),(-1,0),(-1,0)],[(0,-1),(0,1),(-1,0),(0,0)],[(0,-1),(0,0),(0,0),(-1,0)],[(0,-1),(0,0),(-1,0),(0,0)],[(0,-1),(0,1),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(1,-1),(0,0),(-1,0),(0,0)],[(0,-1),(0,1),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(0,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(0,0),(-1,0),(1,0)],[(0,-1),(0,1),(-1,0),(2,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(0,0),(0,0),(2,0)]],[[(1,0),(0,0),(0,0),(-1,0)],[(0,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(2,0)],[(0,-1),(1,0),(-1,0),(0,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(2,0)],[(0,-1),(0,0),(0,0),(2,0)],[(0,0),(0,0),(-1,0),(-1,0)],[(-1,0),(0,1),(-1,0),(0,0)],[(-1,0),(0,0),(0,0),(-1,0)],[(-1,0),(0,0),(-1,0),(0,0)],[(-1,0),(0,1),(-1,0),(1,0)],[(-1,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(-1,0),(0,0)],[(-1,0),(0,1),(-1,0),(1,0)],[(-1,0),(0,0),(0,0),(0,0)],[(-1,0),(0,0),(0,0),(1,0)],[(-1,0),(0,0),(-1,0),(1,0)],[(-1,0),(0,1),(-1,0),(2,0)],[(-1,0),(0,0),(0,0),(1,0)],[(-1,0),(0,0),(0,0),(2,0)]]]
def system23 : List (List Delta) := [[[(1,0),(0,0),(0,0),(-1,0)],[(0,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(2,0)],[(0,-1),(1,0),(-1,0),(0,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(2,0)],[(0,-1),(0,0),(0,0),(2,0)],[(1,-1),(0,0),(-1,0),(-1,0)],[(0,-1),(0,1),(-1,0),(0,0)],[(0,-1),(0,0),(0,0),(-1,0)],[(0,-1),(0,0),(-1,0),(0,0)],[(0,-1),(0,1),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(1,-1),(0,0),(-1,0),(0,0)],[(0,-1),(0,1),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(0,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(0,0),(-1,0),(1,0)],[(0,-1),(0,1),(-1,0),(2,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(0,0),(0,0),(2,0)]],[[(1,0),(0,0),(0,0),(-1,0)],[(0,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(2,0)],[(0,-1),(1,0),(-1,0),(0,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(2,0)],[(0,-1),(0,0),(0,0),(2,0)],[(1,-1),(0,0),(-1,0),(-1,0)],[(0,-1),(0,1),(-1,0),(0,0)],[(0,-1),(0,0),(0,0),(-1,0)],[(0,-1),(0,0),(-1,0),(0,0)],[(0,-1),(0,1),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(1,-1),(0,0),(-1,0),(0,0)],[(0,-1),(0,1),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(0,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(0,0),(-1,0),(1,0)],[(0,-1),(0,1),(-1,0),(2,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(0,0),(0,0),(2,0)]]]
def system24 : List (List Delta) := [[[(1,0),(0,0),(0,0),(-1,0)],[(1,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(2,0)],[(0,-1),(1,0),(-1,0),(0,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(2,0)],[(0,-1),(0,0),(0,0),(2,0)],[(1,-1),(0,0),(-1,0),(-1,0)],[(0,-1),(0,1),(-1,0),(0,0)],[(1,-1),(0,0),(0,0),(-1,0)],[(1,-1),(0,0),(-1,0),(0,0)],[(0,-1),(0,1),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(1,-1),(0,0),(-1,0),(0,0)],[(0,-1),(0,1),(-1,0),(1,0)],[(1,-1),(0,0),(0,0),(0,0)],[(0,-1),(0,0),(0,0),(1,0)],[(1,-1),(0,0),(-1,0),(1,0)],[(0,-1),(0,1),(-1,0),(2,0)],[(1,-1),(0,0),(0,0),(1,0)],[(0,-1),(0,0),(0,0),(2,0)]],[[(1,0),(0,0),(0,0),(-1,0)],[(1,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(2,0)],[(0,-1),(1,0),(-1,0),(0,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(0,0),(0,0),(1,0)],[(0,-1),(1,0),(-1,0),(2,0)],[(0,-1),(0,0),(0,0),(2,0)],[(0,0),(0,0),(-1,0),(-1,0)],[(-1,0),(0,1),(-1,0),(0,0)],[(0,0),(0,0),(0,0),(-1,0)],[(0,0),(0,0),(-1,0),(0,0)],[(-1,0),(0,1),(-1,0),(1,0)],[(-1,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(-1,0),(0,0)],[(-1,0),(0,1),(-1,0),(1,0)],[(0,0),(0,0),(0,0),(0,0)],[(-1,0),(0,0),(0,0),(1,0)],[(0,0),(0,0),(-1,0),(1,0)],[(-1,0),(0,1),(-1,0),(2,0)],[(0,0),(0,0),(0,0),(1,0)],[(-1,0),(0,0),(0,0),(2,0)]]]
def system25 : List (List Delta) := [[[(1,0),(-1,0),(0,0),(0,-1)],[(1,0),(-1,0),(1,0),(0,-1)],[(0,1),(0,0),(1,0),(0,-1)],[(1,0),(0,0),(0,0),(0,-1)],[(0,0),(1,0),(0,0),(0,0)],[(1,0),(0,0),(1,0),(0,-1)],[(0,0),(1,0),(1,0),(0,-1)],[(0,-1),(0,0),(-1,0),(1,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,-1),(1,0),(0,0),(0,1)],[(0,-1),(0,0),(0,0),(1,0)],[(0,0),(0,0),(1,0),(0,0)],[(0,-1),(1,0),(0,0),(1,0)],[(0,0),(1,0),(1,0),(0,0)],[(0,-1),(1,0),(-1,0),(1,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,-1),(2,0),(-1,0),(1,0)],[(0,-1),(2,0),(0,0),(0,1)],[(0,-1),(1,0),(0,0),(1,0)],[(0,0),(1,0),(1,0),(0,0)],[(0,-1),(2,0),(0,0),(1,0)],[(0,-1),(2,0),(1,0),(0,0)]]]
def system26 : List (List Delta) := [[[(-2,0),(2,0)],[(-1,0),(0,0)],[(-1,0),(0,0)]]]
def system27 : List (List Delta) := [[[(-2,0),(2,0)],[(-1,0),(1,0)],[(-1,0),(1,0)]]]
def system28 : List (List Delta) := [[[(-2,0),(2,0)],[(-1,0),(1,0)],[(-1,0),(0,0)]]]
def system29 : List (List Delta) := [[[(-2,0),(2,0)],[(-1,0),(0,0)],[(-1,0),(1,0)]]]
def system30 : List (List Delta) := [[[(-1,0),(2,0)],[(0,0),(0,0)],[(1,0),(0,0)]]]
def system31 : List (List Delta) := [[[(-1,0),(1,0)],[(0,0),(0,0)],[(1,0),(-1,0)]]]
def system32 : List (List Delta) := [[[(-1,0),(2,0)],[(0,0),(1,0)],[(1,0),(0,0)]]]
def system33 : List (List Delta) := [[[(-1,0),(1,0)],[(0,0),(-1,0)],[(1,0),(-1,0)]]]
def system34 : List (List Delta) := [[[(-1,0),(1,-1)],[(0,0),(1,-1)],[(1,0),(0,-1)]]]
def system35 : List (List Delta) := [[[(-2,0),(1,0)],[(-1,0),(1,0)],[(-1,0),(0,1)]]]
def system36 : List (List Delta) := [[[(-2,0),(2,0)],[(-1,0),(1,0)],[(-1,0),(0,0)],[(-1,0),(1,0)],[(0,0),(0,0)],[(0,0),(0,0)],[(1,0),(0,0)]]]
def system37 : List (List Delta) := [[[(-2,0),(2,0)],[(-1,0),(1,0)],[(-1,0),(1,0)],[(-1,0),(2,0)],[(0,0),(1,0)],[(0,0),(1,0)],[(1,0),(0,0)]]]
def system38 : List (List Delta) := [[[(-1,0),(2,0)],[(0,0),(1,0)],[(1,0),(0,0)],[(0,0),(1,0)],[(1,0),(0,0)],[(1,0),(0,0)],[(2,0),(0,0)]]]
def system39 : List (List Delta) := [[[(-1,0),(1,0)],[(0,0),(0,0)],[(1,0),(-1,0)],[(0,0),(1,0)],[(1,0),(0,0)],[(1,0),(0,0)],[(2,0),(-1,0)]]]
def system40 : List (List Delta) := [[[(1,0),(0,-1),(-1,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],[(1,0),(0,-1),(-1,0),(1,0),(0,0),(0,0),(0,0),(0,0),(0,1)],[(0,1),(1,0),(0,0),(0,0),(1,0),(-1,0),(0,0),(0,0),(0,-1)],[(0,0),(1,0),(0,0),(0,0),(0,0),(-1,0),(0,0),(0,0),(0,-1)],[(0,-1),(0,1),(0,0),(0,0),(0,0),(0,0),(-1,0),(1,0),(1,0)],[(0,-1),(0,0),(0,0),(0,0),(0,0),(0,0),(-1,0),(0,0),(1,0)]]]
def system41 : List (List Delta) := [[[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(-1,0),(1,0),(1,0)],[(1,0),(0,0),(-1,0),(0,0)],[(1,0),(1,0),(-1,0),(0,0)],[(0,0),(1,0),(0,0),(-1,0)],[(-1,0),(0,0),(1,0),(0,0)]]]
def system42 : List (List Delta) := [[[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(-1,0),(1,0),(1,0)],[(1,0),(0,0),(-1,0),(0,0)],[(1,0),(1,0),(-1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(-1,0),(-1,0),(1,0),(1,0)]]]
def system43 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(0,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(1,0),(-1,0),(0,0),(0,0)],[(1,0),(0,0),(0,0),(0,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(0,0),(-1,0),(1,0),(0,0)],[(-1,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(1,0),(-1,0),(0,0),(0,0)],[(1,0),(0,0),(0,0),(0,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(-1,0),(0,0),(0,0),(1,0)],[(0,0),(-1,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(0,0)],[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(0,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)]]]
def system44 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(0,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(1,0),(-1,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(0,0),(-1,0),(1,0),(1,0)],[(-1,0),(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(1,0),(-1,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(-1,0),(0,0),(0,0),(1,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(1,0)],[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(0,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)]]]
def system45 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(1,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(1,0),(-1,0),(0,0),(0,0)],[(1,0),(0,0),(0,0),(0,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(0,0),(-1,0),(1,0),(0,0)],[(-1,0),(0,0),(1,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(1,0),(-1,0),(0,0),(0,0)],[(1,0),(0,0),(0,0),(0,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(-1,0),(0,0),(1,0),(1,0)],[(0,0),(-1,0),(0,0),(0,0)],[(0,0),(0,0),(0,0),(0,0)],[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(1,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)]]]
def system46 : List (List Delta) := [[[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(1,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(1,0),(-1,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(0,0),(-1,0),(1,0),(1,0)],[(-1,0),(0,0),(1,0),(0,0)],[(0,0),(0,0),(1,0),(0,0)],[(0,0),(-1,0),(0,0),(1,0)],[(1,0),(-1,0),(0,0),(1,0)],[(1,0),(0,0),(0,0),(0,0)],[(-1,0),(-1,0),(1,0),(1,0)],[(-1,0),(0,0),(1,0),(1,0)],[(0,0),(-1,0),(0,0),(1,0)],[(0,0),(0,0),(0,0),(1,0)],[(-1,0),(0,0),(1,0),(0,0)],[(-1,0),(1,0),(1,0),(0,0)],[(0,0),(1,0),(0,0),(0,0)]]]
def allSystems : List (List (List Delta)) := [system0,system1,system2,system3,system4,system5,system6,system7,system8,system9,system10,system11,system12,system13,system14,system15,system16,system17,system18,system19,system20,system21,system22,system23,system24,system25,system26,system27,system28,system29,system30,system31,system32,system33,system34,system35,system36,system37,system38,system39,system40,system41,system42,system43,system44,system45,system46]
structure Assignment where
  pattern : Nat
  modes : List Mode
  subject : Bool
  system : Nat
  deriving DecidableEq, Repr
def assignments0 : List Assignment := [⟨0,[(true,true),(true,true)],false,0⟩,⟨0,[(true,true),(true,true)],true,0⟩,⟨0,[(true,true),(false,false)],false,1⟩,⟨0,[(true,true),(false,false)],true,1⟩,⟨0,[(true,true),(true,false)],false,0⟩,⟨0,[(true,true),(true,false)],true,0⟩,⟨0,[(true,true),(false,true)],false,1⟩,⟨0,[(true,true),(false,true)],true,1⟩,⟨0,[(false,false),(true,true)],false,0⟩,⟨0,[(false,false),(true,true)],true,0⟩,⟨0,[(false,false),(false,false)],false,1⟩,⟨0,[(false,false),(false,false)],true,1⟩,⟨0,[(false,false),(true,false)],false,0⟩,⟨0,[(false,false),(true,false)],true,0⟩,⟨0,[(false,false),(false,true)],false,1⟩,⟨0,[(false,false),(false,true)],true,1⟩,⟨0,[(true,false),(true,true)],false,0⟩,⟨0,[(true,false),(true,true)],true,0⟩,⟨0,[(true,false),(false,false)],false,1⟩,⟨0,[(true,false),(false,false)],true,1⟩,⟨0,[(true,false),(true,false)],false,0⟩,⟨0,[(true,false),(true,false)],true,0⟩,⟨0,[(true,false),(false,true)],false,1⟩,⟨0,[(true,false),(false,true)],true,1⟩,⟨0,[(false,true),(true,true)],false,0⟩,⟨0,[(false,true),(true,true)],true,0⟩,⟨0,[(false,true),(false,false)],false,1⟩,⟨0,[(false,true),(false,false)],true,1⟩,⟨0,[(false,true),(true,false)],false,0⟩,⟨0,[(false,true),(true,false)],true,0⟩,⟨0,[(false,true),(false,true)],false,1⟩,⟨0,[(false,true),(false,true)],true,1⟩]
def assignments1 : List Assignment := [⟨1,[(true,true),(true,true)],false,2⟩,⟨1,[(true,true),(true,true)],true,2⟩,⟨1,[(true,true),(false,false)],false,3⟩,⟨1,[(true,true),(false,false)],true,3⟩,⟨1,[(true,true),(true,false)],false,2⟩,⟨1,[(true,true),(true,false)],true,2⟩,⟨1,[(true,true),(false,true)],false,3⟩,⟨1,[(true,true),(false,true)],true,3⟩,⟨1,[(false,false),(true,true)],false,2⟩,⟨1,[(false,false),(true,true)],true,2⟩,⟨1,[(false,false),(false,false)],false,3⟩,⟨1,[(false,false),(false,false)],true,3⟩,⟨1,[(false,false),(true,false)],false,2⟩,⟨1,[(false,false),(true,false)],true,2⟩,⟨1,[(false,false),(false,true)],false,3⟩,⟨1,[(false,false),(false,true)],true,3⟩,⟨1,[(true,false),(true,true)],false,2⟩,⟨1,[(true,false),(true,true)],true,2⟩,⟨1,[(true,false),(false,false)],false,3⟩,⟨1,[(true,false),(false,false)],true,3⟩,⟨1,[(true,false),(true,false)],false,2⟩,⟨1,[(true,false),(true,false)],true,2⟩,⟨1,[(true,false),(false,true)],false,3⟩,⟨1,[(true,false),(false,true)],true,3⟩,⟨1,[(false,true),(true,true)],false,2⟩,⟨1,[(false,true),(true,true)],true,2⟩,⟨1,[(false,true),(false,false)],false,3⟩,⟨1,[(false,true),(false,false)],true,3⟩,⟨1,[(false,true),(true,false)],false,2⟩,⟨1,[(false,true),(true,false)],true,2⟩,⟨1,[(false,true),(false,true)],false,3⟩,⟨1,[(false,true),(false,true)],true,3⟩]
def assignments2 : List Assignment := [⟨2,[(true,true),(true,true)],false,4⟩,⟨2,[(true,true),(true,true)],true,4⟩,⟨2,[(true,true),(false,false)],false,4⟩,⟨2,[(true,true),(false,false)],true,4⟩,⟨2,[(true,true),(true,false)],false,4⟩,⟨2,[(true,true),(true,false)],true,4⟩,⟨2,[(true,true),(false,true)],false,4⟩,⟨2,[(true,true),(false,true)],true,4⟩,⟨2,[(false,false),(true,true)],false,5⟩,⟨2,[(false,false),(true,true)],true,5⟩,⟨2,[(false,false),(false,false)],false,5⟩,⟨2,[(false,false),(false,false)],true,5⟩,⟨2,[(false,false),(true,false)],false,5⟩,⟨2,[(false,false),(true,false)],true,5⟩,⟨2,[(false,false),(false,true)],false,5⟩,⟨2,[(false,false),(false,true)],true,5⟩,⟨2,[(true,false),(true,true)],false,5⟩,⟨2,[(true,false),(true,true)],true,5⟩,⟨2,[(true,false),(false,false)],false,5⟩,⟨2,[(true,false),(false,false)],true,5⟩,⟨2,[(true,false),(true,false)],false,5⟩,⟨2,[(true,false),(true,false)],true,5⟩,⟨2,[(true,false),(false,true)],false,5⟩,⟨2,[(true,false),(false,true)],true,5⟩,⟨2,[(false,true),(true,true)],false,4⟩,⟨2,[(false,true),(true,true)],true,4⟩,⟨2,[(false,true),(false,false)],false,4⟩,⟨2,[(false,true),(false,false)],true,4⟩,⟨2,[(false,true),(true,false)],false,4⟩,⟨2,[(false,true),(true,false)],true,4⟩,⟨2,[(false,true),(false,true)],false,4⟩,⟨2,[(false,true),(false,true)],true,4⟩]
def assignments3 : List Assignment := [⟨3,[(true,true),(true,true)],false,6⟩,⟨3,[(true,true),(true,true)],true,6⟩,⟨3,[(true,true),(false,false)],false,6⟩,⟨3,[(true,true),(false,false)],true,6⟩,⟨3,[(true,true),(true,false)],false,6⟩,⟨3,[(true,true),(true,false)],true,6⟩,⟨3,[(true,true),(false,true)],false,6⟩,⟨3,[(true,true),(false,true)],true,6⟩,⟨3,[(false,false),(true,true)],false,7⟩,⟨3,[(false,false),(true,true)],true,7⟩,⟨3,[(false,false),(false,false)],false,7⟩,⟨3,[(false,false),(false,false)],true,7⟩,⟨3,[(false,false),(true,false)],false,7⟩,⟨3,[(false,false),(true,false)],true,7⟩,⟨3,[(false,false),(false,true)],false,7⟩,⟨3,[(false,false),(false,true)],true,7⟩,⟨3,[(true,false),(true,true)],false,7⟩,⟨3,[(true,false),(true,true)],true,7⟩,⟨3,[(true,false),(false,false)],false,7⟩,⟨3,[(true,false),(false,false)],true,7⟩,⟨3,[(true,false),(true,false)],false,7⟩,⟨3,[(true,false),(true,false)],true,7⟩,⟨3,[(true,false),(false,true)],false,7⟩,⟨3,[(true,false),(false,true)],true,7⟩,⟨3,[(false,true),(true,true)],false,6⟩,⟨3,[(false,true),(true,true)],true,6⟩,⟨3,[(false,true),(false,false)],false,6⟩,⟨3,[(false,true),(false,false)],true,6⟩,⟨3,[(false,true),(true,false)],false,6⟩,⟨3,[(false,true),(true,false)],true,6⟩,⟨3,[(false,true),(false,true)],false,6⟩,⟨3,[(false,true),(false,true)],true,6⟩]
def assignments4 : List Assignment := [⟨4,[(true,true),(true,true)],false,8⟩,⟨4,[(true,true),(true,true)],true,8⟩,⟨4,[(true,true),(false,false)],false,9⟩,⟨4,[(true,true),(false,false)],true,9⟩,⟨4,[(true,true),(true,false)],false,8⟩,⟨4,[(true,true),(true,false)],true,8⟩,⟨4,[(true,true),(false,true)],false,9⟩,⟨4,[(true,true),(false,true)],true,9⟩,⟨4,[(false,false),(true,true)],false,10⟩,⟨4,[(false,false),(true,true)],true,10⟩,⟨4,[(false,false),(false,false)],false,11⟩,⟨4,[(false,false),(false,false)],true,11⟩,⟨4,[(false,false),(true,false)],false,10⟩,⟨4,[(false,false),(true,false)],true,10⟩,⟨4,[(false,false),(false,true)],false,11⟩,⟨4,[(false,false),(false,true)],true,11⟩,⟨4,[(true,false),(true,true)],false,10⟩,⟨4,[(true,false),(true,true)],true,10⟩,⟨4,[(true,false),(false,false)],false,11⟩,⟨4,[(true,false),(false,false)],true,11⟩,⟨4,[(true,false),(true,false)],false,10⟩,⟨4,[(true,false),(true,false)],true,10⟩,⟨4,[(true,false),(false,true)],false,11⟩,⟨4,[(true,false),(false,true)],true,11⟩,⟨4,[(false,true),(true,true)],false,8⟩,⟨4,[(false,true),(true,true)],true,8⟩,⟨4,[(false,true),(false,false)],false,9⟩,⟨4,[(false,true),(false,false)],true,9⟩,⟨4,[(false,true),(true,false)],false,8⟩,⟨4,[(false,true),(true,false)],true,8⟩,⟨4,[(false,true),(false,true)],false,9⟩,⟨4,[(false,true),(false,true)],true,9⟩]
def assignments5 : List Assignment := [⟨5,[(true,true),(true,true)],false,12⟩,⟨5,[(true,true),(true,true)],true,12⟩,⟨5,[(true,true),(false,false)],false,13⟩,⟨5,[(true,true),(false,false)],true,13⟩,⟨5,[(true,true),(true,false)],false,12⟩,⟨5,[(true,true),(true,false)],true,12⟩,⟨5,[(true,true),(false,true)],false,13⟩,⟨5,[(true,true),(false,true)],true,13⟩,⟨5,[(false,false),(true,true)],false,14⟩,⟨5,[(false,false),(true,true)],true,14⟩,⟨5,[(false,false),(false,false)],false,15⟩,⟨5,[(false,false),(false,false)],true,15⟩,⟨5,[(false,false),(true,false)],false,14⟩,⟨5,[(false,false),(true,false)],true,14⟩,⟨5,[(false,false),(false,true)],false,15⟩,⟨5,[(false,false),(false,true)],true,15⟩,⟨5,[(true,false),(true,true)],false,14⟩,⟨5,[(true,false),(true,true)],true,14⟩,⟨5,[(true,false),(false,false)],false,15⟩,⟨5,[(true,false),(false,false)],true,15⟩,⟨5,[(true,false),(true,false)],false,14⟩,⟨5,[(true,false),(true,false)],true,14⟩,⟨5,[(true,false),(false,true)],false,15⟩,⟨5,[(true,false),(false,true)],true,15⟩,⟨5,[(false,true),(true,true)],false,12⟩,⟨5,[(false,true),(true,true)],true,12⟩,⟨5,[(false,true),(false,false)],false,13⟩,⟨5,[(false,true),(false,false)],true,13⟩,⟨5,[(false,true),(true,false)],false,12⟩,⟨5,[(false,true),(true,false)],true,12⟩,⟨5,[(false,true),(false,true)],false,13⟩,⟨5,[(false,true),(false,true)],true,13⟩]
def assignments6 : List Assignment := [⟨6,[(true,true),(true,true)],false,16⟩,⟨6,[(true,true),(true,true)],true,16⟩,⟨6,[(true,true),(false,false)],false,17⟩,⟨6,[(true,true),(false,false)],true,17⟩,⟨6,[(true,true),(true,false)],false,16⟩,⟨6,[(true,true),(true,false)],true,16⟩,⟨6,[(true,true),(false,true)],false,17⟩,⟨6,[(true,true),(false,true)],true,17⟩,⟨6,[(false,false),(true,true)],false,18⟩,⟨6,[(false,false),(true,true)],true,18⟩,⟨6,[(false,false),(false,false)],false,19⟩,⟨6,[(false,false),(false,false)],true,19⟩,⟨6,[(false,false),(true,false)],false,18⟩,⟨6,[(false,false),(true,false)],true,18⟩,⟨6,[(false,false),(false,true)],false,19⟩,⟨6,[(false,false),(false,true)],true,19⟩,⟨6,[(true,false),(true,true)],false,18⟩,⟨6,[(true,false),(true,true)],true,18⟩,⟨6,[(true,false),(false,false)],false,19⟩,⟨6,[(true,false),(false,false)],true,19⟩,⟨6,[(true,false),(true,false)],false,18⟩,⟨6,[(true,false),(true,false)],true,18⟩,⟨6,[(true,false),(false,true)],false,19⟩,⟨6,[(true,false),(false,true)],true,19⟩,⟨6,[(false,true),(true,true)],false,16⟩,⟨6,[(false,true),(true,true)],true,16⟩,⟨6,[(false,true),(false,false)],false,17⟩,⟨6,[(false,true),(false,false)],true,17⟩,⟨6,[(false,true),(true,false)],false,16⟩,⟨6,[(false,true),(true,false)],true,16⟩,⟨6,[(false,true),(false,true)],false,17⟩,⟨6,[(false,true),(false,true)],true,17⟩]
def assignments7 : List Assignment := [⟨7,[(true,true),(true,true)],false,20⟩,⟨7,[(true,true),(true,true)],true,20⟩,⟨7,[(true,true),(false,false)],false,21⟩,⟨7,[(true,true),(false,false)],true,21⟩,⟨7,[(true,true),(true,false)],false,20⟩,⟨7,[(true,true),(true,false)],true,20⟩,⟨7,[(true,true),(false,true)],false,21⟩,⟨7,[(true,true),(false,true)],true,21⟩,⟨7,[(false,false),(true,true)],false,20⟩,⟨7,[(false,false),(true,true)],true,20⟩,⟨7,[(false,false),(false,false)],false,21⟩,⟨7,[(false,false),(false,false)],true,21⟩,⟨7,[(false,false),(true,false)],false,20⟩,⟨7,[(false,false),(true,false)],true,20⟩,⟨7,[(false,false),(false,true)],false,21⟩,⟨7,[(false,false),(false,true)],true,21⟩,⟨7,[(true,false),(true,true)],false,20⟩,⟨7,[(true,false),(true,true)],true,20⟩,⟨7,[(true,false),(false,false)],false,21⟩,⟨7,[(true,false),(false,false)],true,21⟩,⟨7,[(true,false),(true,false)],false,20⟩,⟨7,[(true,false),(true,false)],true,20⟩,⟨7,[(true,false),(false,true)],false,21⟩,⟨7,[(true,false),(false,true)],true,21⟩,⟨7,[(false,true),(true,true)],false,20⟩,⟨7,[(false,true),(true,true)],true,20⟩,⟨7,[(false,true),(false,false)],false,21⟩,⟨7,[(false,true),(false,false)],true,21⟩,⟨7,[(false,true),(true,false)],false,20⟩,⟨7,[(false,true),(true,false)],true,20⟩,⟨7,[(false,true),(false,true)],false,21⟩,⟨7,[(false,true),(false,true)],true,21⟩]
def assignments8 : List Assignment := [⟨8,[(true,true),(true,true)],false,22⟩,⟨8,[(true,true),(true,true)],true,23⟩,⟨8,[(true,true),(false,false)],false,22⟩,⟨8,[(true,true),(false,false)],true,23⟩,⟨8,[(true,true),(true,false)],false,22⟩,⟨8,[(true,true),(true,false)],true,23⟩,⟨8,[(true,true),(false,true)],false,22⟩,⟨8,[(true,true),(false,true)],true,23⟩,⟨8,[(false,false),(true,true)],false,24⟩,⟨8,[(false,false),(true,true)],true,24⟩,⟨8,[(false,false),(false,false)],false,24⟩,⟨8,[(false,false),(false,false)],true,24⟩,⟨8,[(false,false),(true,false)],false,24⟩,⟨8,[(false,false),(true,false)],true,24⟩,⟨8,[(false,false),(false,true)],false,24⟩,⟨8,[(false,false),(false,true)],true,24⟩,⟨8,[(true,false),(true,true)],false,22⟩,⟨8,[(true,false),(true,true)],true,23⟩,⟨8,[(true,false),(false,false)],false,22⟩,⟨8,[(true,false),(false,false)],true,23⟩,⟨8,[(true,false),(true,false)],false,22⟩,⟨8,[(true,false),(true,false)],true,23⟩,⟨8,[(true,false),(false,true)],false,22⟩,⟨8,[(true,false),(false,true)],true,23⟩,⟨8,[(false,true),(true,true)],false,24⟩,⟨8,[(false,true),(true,true)],true,24⟩,⟨8,[(false,true),(false,false)],false,24⟩,⟨8,[(false,true),(false,false)],true,24⟩,⟨8,[(false,true),(true,false)],false,24⟩,⟨8,[(false,true),(true,false)],true,24⟩,⟨8,[(false,true),(false,true)],false,24⟩,⟨8,[(false,true),(false,true)],true,24⟩]
def assignments9 : List Assignment := [⟨9,[(true,true),(true,true)],false,25⟩,⟨9,[(true,true),(true,true)],true,25⟩,⟨9,[(true,true),(false,false)],false,25⟩,⟨9,[(true,true),(false,false)],true,25⟩,⟨9,[(true,true),(true,false)],false,25⟩,⟨9,[(true,true),(true,false)],true,25⟩,⟨9,[(true,true),(false,true)],false,25⟩,⟨9,[(true,true),(false,true)],true,25⟩,⟨9,[(false,false),(true,true)],false,25⟩,⟨9,[(false,false),(true,true)],true,25⟩,⟨9,[(false,false),(false,false)],false,25⟩,⟨9,[(false,false),(false,false)],true,25⟩,⟨9,[(false,false),(true,false)],false,25⟩,⟨9,[(false,false),(true,false)],true,25⟩,⟨9,[(false,false),(false,true)],false,25⟩,⟨9,[(false,false),(false,true)],true,25⟩,⟨9,[(true,false),(true,true)],false,25⟩,⟨9,[(true,false),(true,true)],true,25⟩,⟨9,[(true,false),(false,false)],false,25⟩,⟨9,[(true,false),(false,false)],true,25⟩,⟨9,[(true,false),(true,false)],false,25⟩,⟨9,[(true,false),(true,false)],true,25⟩,⟨9,[(true,false),(false,true)],false,25⟩,⟨9,[(true,false),(false,true)],true,25⟩,⟨9,[(false,true),(true,true)],false,25⟩,⟨9,[(false,true),(true,true)],true,25⟩,⟨9,[(false,true),(false,false)],false,25⟩,⟨9,[(false,true),(false,false)],true,25⟩,⟨9,[(false,true),(true,false)],false,25⟩,⟨9,[(false,true),(true,false)],true,25⟩,⟨9,[(false,true),(false,true)],false,25⟩,⟨9,[(false,true),(false,true)],true,25⟩]
def assignments10 : List Assignment := [⟨10,[(true,true)],false,26⟩,⟨10,[(true,true)],true,26⟩,⟨10,[(false,false)],false,27⟩,⟨10,[(false,false)],true,27⟩,⟨10,[(true,false)],false,28⟩,⟨10,[(true,false)],true,28⟩,⟨10,[(false,true)],false,29⟩,⟨10,[(false,true)],true,29⟩]
def assignments11 : List Assignment := [⟨11,[(true,true)],false,30⟩,⟨11,[(true,true)],true,30⟩,⟨11,[(false,false)],false,31⟩,⟨11,[(false,false)],true,31⟩,⟨11,[(true,false)],false,32⟩,⟨11,[(true,false)],true,32⟩,⟨11,[(false,true)],false,33⟩,⟨11,[(false,true)],true,33⟩]
def assignments12 : List Assignment := [⟨12,[(true,true)],false,30⟩,⟨12,[(true,true)],true,30⟩,⟨12,[(false,false)],false,31⟩,⟨12,[(false,false)],true,31⟩,⟨12,[(true,false)],false,33⟩,⟨12,[(true,false)],true,33⟩,⟨12,[(false,true)],false,32⟩,⟨12,[(false,true)],true,32⟩]
def assignments13 : List Assignment := [⟨13,[(true,true)],false,34⟩,⟨13,[(true,true)],true,34⟩,⟨13,[(false,false)],false,34⟩,⟨13,[(false,false)],true,34⟩,⟨13,[(true,false)],false,34⟩,⟨13,[(true,false)],true,34⟩,⟨13,[(false,true)],false,34⟩,⟨13,[(false,true)],true,34⟩]
def assignments14 : List Assignment := [⟨14,[(true,true)],false,35⟩,⟨14,[(true,true)],true,35⟩,⟨14,[(false,false)],false,35⟩,⟨14,[(false,false)],true,35⟩,⟨14,[(true,false)],false,35⟩,⟨14,[(true,false)],true,35⟩,⟨14,[(false,true)],false,35⟩,⟨14,[(false,true)],true,35⟩]
def assignments15 : List Assignment := [⟨15,[(true,true)],false,36⟩,⟨15,[(true,true)],true,36⟩,⟨15,[(false,false)],false,37⟩,⟨15,[(false,false)],true,37⟩,⟨15,[(true,false)],false,36⟩,⟨15,[(true,false)],true,36⟩,⟨15,[(false,true)],false,37⟩,⟨15,[(false,true)],true,37⟩]
def assignments16 : List Assignment := [⟨16,[(true,true)],false,38⟩,⟨16,[(true,true)],true,38⟩,⟨16,[(false,false)],false,39⟩,⟨16,[(false,false)],true,39⟩,⟨16,[(true,false)],false,38⟩,⟨16,[(true,false)],true,38⟩,⟨16,[(false,true)],false,39⟩,⟨16,[(false,true)],true,39⟩]
def assignments17 : List Assignment := [⟨17,[(true,true),(true,true),(true,true)],false,40⟩,⟨17,[(true,true),(true,true),(true,true)],true,40⟩,⟨17,[(true,true),(true,true),(false,false)],false,40⟩,⟨17,[(true,true),(true,true),(false,false)],true,40⟩,⟨17,[(true,true),(true,true),(true,false)],false,40⟩,⟨17,[(true,true),(true,true),(true,false)],true,40⟩,⟨17,[(true,true),(true,true),(false,true)],false,40⟩,⟨17,[(true,true),(true,true),(false,true)],true,40⟩,⟨17,[(true,true),(false,false),(true,true)],false,40⟩,⟨17,[(true,true),(false,false),(true,true)],true,40⟩,⟨17,[(true,true),(false,false),(false,false)],false,40⟩,⟨17,[(true,true),(false,false),(false,false)],true,40⟩,⟨17,[(true,true),(false,false),(true,false)],false,40⟩,⟨17,[(true,true),(false,false),(true,false)],true,40⟩,⟨17,[(true,true),(false,false),(false,true)],false,40⟩,⟨17,[(true,true),(false,false),(false,true)],true,40⟩,⟨17,[(true,true),(true,false),(true,true)],false,40⟩,⟨17,[(true,true),(true,false),(true,true)],true,40⟩,⟨17,[(true,true),(true,false),(false,false)],false,40⟩,⟨17,[(true,true),(true,false),(false,false)],true,40⟩,⟨17,[(true,true),(true,false),(true,false)],false,40⟩,⟨17,[(true,true),(true,false),(true,false)],true,40⟩,⟨17,[(true,true),(true,false),(false,true)],false,40⟩,⟨17,[(true,true),(true,false),(false,true)],true,40⟩,⟨17,[(true,true),(false,true),(true,true)],false,40⟩,⟨17,[(true,true),(false,true),(true,true)],true,40⟩,⟨17,[(true,true),(false,true),(false,false)],false,40⟩,⟨17,[(true,true),(false,true),(false,false)],true,40⟩,⟨17,[(true,true),(false,true),(true,false)],false,40⟩,⟨17,[(true,true),(false,true),(true,false)],true,40⟩,⟨17,[(true,true),(false,true),(false,true)],false,40⟩,⟨17,[(true,true),(false,true),(false,true)],true,40⟩,⟨17,[(false,false),(true,true),(true,true)],false,40⟩,⟨17,[(false,false),(true,true),(true,true)],true,40⟩,⟨17,[(false,false),(true,true),(false,false)],false,40⟩,⟨17,[(false,false),(true,true),(false,false)],true,40⟩,⟨17,[(false,false),(true,true),(true,false)],false,40⟩,⟨17,[(false,false),(true,true),(true,false)],true,40⟩,⟨17,[(false,false),(true,true),(false,true)],false,40⟩,⟨17,[(false,false),(true,true),(false,true)],true,40⟩,⟨17,[(false,false),(false,false),(true,true)],false,40⟩,⟨17,[(false,false),(false,false),(true,true)],true,40⟩,⟨17,[(false,false),(false,false),(false,false)],false,40⟩,⟨17,[(false,false),(false,false),(false,false)],true,40⟩,⟨17,[(false,false),(false,false),(true,false)],false,40⟩,⟨17,[(false,false),(false,false),(true,false)],true,40⟩,⟨17,[(false,false),(false,false),(false,true)],false,40⟩,⟨17,[(false,false),(false,false),(false,true)],true,40⟩,⟨17,[(false,false),(true,false),(true,true)],false,40⟩,⟨17,[(false,false),(true,false),(true,true)],true,40⟩,⟨17,[(false,false),(true,false),(false,false)],false,40⟩,⟨17,[(false,false),(true,false),(false,false)],true,40⟩,⟨17,[(false,false),(true,false),(true,false)],false,40⟩,⟨17,[(false,false),(true,false),(true,false)],true,40⟩,⟨17,[(false,false),(true,false),(false,true)],false,40⟩,⟨17,[(false,false),(true,false),(false,true)],true,40⟩,⟨17,[(false,false),(false,true),(true,true)],false,40⟩,⟨17,[(false,false),(false,true),(true,true)],true,40⟩,⟨17,[(false,false),(false,true),(false,false)],false,40⟩,⟨17,[(false,false),(false,true),(false,false)],true,40⟩,⟨17,[(false,false),(false,true),(true,false)],false,40⟩,⟨17,[(false,false),(false,true),(true,false)],true,40⟩,⟨17,[(false,false),(false,true),(false,true)],false,40⟩,⟨17,[(false,false),(false,true),(false,true)],true,40⟩,⟨17,[(true,false),(true,true),(true,true)],false,40⟩,⟨17,[(true,false),(true,true),(true,true)],true,40⟩,⟨17,[(true,false),(true,true),(false,false)],false,40⟩,⟨17,[(true,false),(true,true),(false,false)],true,40⟩,⟨17,[(true,false),(true,true),(true,false)],false,40⟩,⟨17,[(true,false),(true,true),(true,false)],true,40⟩,⟨17,[(true,false),(true,true),(false,true)],false,40⟩,⟨17,[(true,false),(true,true),(false,true)],true,40⟩,⟨17,[(true,false),(false,false),(true,true)],false,40⟩,⟨17,[(true,false),(false,false),(true,true)],true,40⟩,⟨17,[(true,false),(false,false),(false,false)],false,40⟩,⟨17,[(true,false),(false,false),(false,false)],true,40⟩,⟨17,[(true,false),(false,false),(true,false)],false,40⟩,⟨17,[(true,false),(false,false),(true,false)],true,40⟩,⟨17,[(true,false),(false,false),(false,true)],false,40⟩,⟨17,[(true,false),(false,false),(false,true)],true,40⟩,⟨17,[(true,false),(true,false),(true,true)],false,40⟩,⟨17,[(true,false),(true,false),(true,true)],true,40⟩,⟨17,[(true,false),(true,false),(false,false)],false,40⟩,⟨17,[(true,false),(true,false),(false,false)],true,40⟩,⟨17,[(true,false),(true,false),(true,false)],false,40⟩,⟨17,[(true,false),(true,false),(true,false)],true,40⟩,⟨17,[(true,false),(true,false),(false,true)],false,40⟩,⟨17,[(true,false),(true,false),(false,true)],true,40⟩,⟨17,[(true,false),(false,true),(true,true)],false,40⟩,⟨17,[(true,false),(false,true),(true,true)],true,40⟩,⟨17,[(true,false),(false,true),(false,false)],false,40⟩,⟨17,[(true,false),(false,true),(false,false)],true,40⟩,⟨17,[(true,false),(false,true),(true,false)],false,40⟩,⟨17,[(true,false),(false,true),(true,false)],true,40⟩,⟨17,[(true,false),(false,true),(false,true)],false,40⟩,⟨17,[(true,false),(false,true),(false,true)],true,40⟩,⟨17,[(false,true),(true,true),(true,true)],false,40⟩,⟨17,[(false,true),(true,true),(true,true)],true,40⟩,⟨17,[(false,true),(true,true),(false,false)],false,40⟩,⟨17,[(false,true),(true,true),(false,false)],true,40⟩,⟨17,[(false,true),(true,true),(true,false)],false,40⟩,⟨17,[(false,true),(true,true),(true,false)],true,40⟩,⟨17,[(false,true),(true,true),(false,true)],false,40⟩,⟨17,[(false,true),(true,true),(false,true)],true,40⟩,⟨17,[(false,true),(false,false),(true,true)],false,40⟩,⟨17,[(false,true),(false,false),(true,true)],true,40⟩,⟨17,[(false,true),(false,false),(false,false)],false,40⟩,⟨17,[(false,true),(false,false),(false,false)],true,40⟩,⟨17,[(false,true),(false,false),(true,false)],false,40⟩,⟨17,[(false,true),(false,false),(true,false)],true,40⟩,⟨17,[(false,true),(false,false),(false,true)],false,40⟩,⟨17,[(false,true),(false,false),(false,true)],true,40⟩,⟨17,[(false,true),(true,false),(true,true)],false,40⟩,⟨17,[(false,true),(true,false),(true,true)],true,40⟩,⟨17,[(false,true),(true,false),(false,false)],false,40⟩,⟨17,[(false,true),(true,false),(false,false)],true,40⟩,⟨17,[(false,true),(true,false),(true,false)],false,40⟩,⟨17,[(false,true),(true,false),(true,false)],true,40⟩,⟨17,[(false,true),(true,false),(false,true)],false,40⟩,⟨17,[(false,true),(true,false),(false,true)],true,40⟩,⟨17,[(false,true),(false,true),(true,true)],false,40⟩,⟨17,[(false,true),(false,true),(true,true)],true,40⟩,⟨17,[(false,true),(false,true),(false,false)],false,40⟩,⟨17,[(false,true),(false,true),(false,false)],true,40⟩,⟨17,[(false,true),(false,true),(true,false)],false,40⟩,⟨17,[(false,true),(false,true),(true,false)],true,40⟩,⟨17,[(false,true),(false,true),(false,true)],false,40⟩,⟨17,[(false,true),(false,true),(false,true)],true,40⟩]
def assignments18 : List Assignment := [⟨18,[(true,true),(true,true)],false,41⟩,⟨18,[(true,true),(true,true)],true,41⟩,⟨18,[(true,true),(false,false)],false,41⟩,⟨18,[(true,true),(false,false)],true,41⟩,⟨18,[(true,true),(true,false)],false,41⟩,⟨18,[(true,true),(true,false)],true,41⟩,⟨18,[(true,true),(false,true)],false,41⟩,⟨18,[(true,true),(false,true)],true,41⟩,⟨18,[(false,false),(true,true)],false,41⟩,⟨18,[(false,false),(true,true)],true,41⟩,⟨18,[(false,false),(false,false)],false,41⟩,⟨18,[(false,false),(false,false)],true,41⟩,⟨18,[(false,false),(true,false)],false,41⟩,⟨18,[(false,false),(true,false)],true,41⟩,⟨18,[(false,false),(false,true)],false,41⟩,⟨18,[(false,false),(false,true)],true,41⟩,⟨18,[(true,false),(true,true)],false,41⟩,⟨18,[(true,false),(true,true)],true,41⟩,⟨18,[(true,false),(false,false)],false,41⟩,⟨18,[(true,false),(false,false)],true,41⟩,⟨18,[(true,false),(true,false)],false,41⟩,⟨18,[(true,false),(true,false)],true,41⟩,⟨18,[(true,false),(false,true)],false,41⟩,⟨18,[(true,false),(false,true)],true,41⟩,⟨18,[(false,true),(true,true)],false,41⟩,⟨18,[(false,true),(true,true)],true,41⟩,⟨18,[(false,true),(false,false)],false,41⟩,⟨18,[(false,true),(false,false)],true,41⟩,⟨18,[(false,true),(true,false)],false,41⟩,⟨18,[(false,true),(true,false)],true,41⟩,⟨18,[(false,true),(false,true)],false,41⟩,⟨18,[(false,true),(false,true)],true,41⟩]
def assignments19 : List Assignment := [⟨19,[(true,true),(true,true)],false,42⟩,⟨19,[(true,true),(true,true)],true,42⟩,⟨19,[(true,true),(false,false)],false,42⟩,⟨19,[(true,true),(false,false)],true,42⟩,⟨19,[(true,true),(true,false)],false,42⟩,⟨19,[(true,true),(true,false)],true,42⟩,⟨19,[(true,true),(false,true)],false,42⟩,⟨19,[(true,true),(false,true)],true,42⟩,⟨19,[(false,false),(true,true)],false,42⟩,⟨19,[(false,false),(true,true)],true,42⟩,⟨19,[(false,false),(false,false)],false,42⟩,⟨19,[(false,false),(false,false)],true,42⟩,⟨19,[(false,false),(true,false)],false,42⟩,⟨19,[(false,false),(true,false)],true,42⟩,⟨19,[(false,false),(false,true)],false,42⟩,⟨19,[(false,false),(false,true)],true,42⟩,⟨19,[(true,false),(true,true)],false,42⟩,⟨19,[(true,false),(true,true)],true,42⟩,⟨19,[(true,false),(false,false)],false,42⟩,⟨19,[(true,false),(false,false)],true,42⟩,⟨19,[(true,false),(true,false)],false,42⟩,⟨19,[(true,false),(true,false)],true,42⟩,⟨19,[(true,false),(false,true)],false,42⟩,⟨19,[(true,false),(false,true)],true,42⟩,⟨19,[(false,true),(true,true)],false,42⟩,⟨19,[(false,true),(true,true)],true,42⟩,⟨19,[(false,true),(false,false)],false,42⟩,⟨19,[(false,true),(false,false)],true,42⟩,⟨19,[(false,true),(true,false)],false,42⟩,⟨19,[(false,true),(true,false)],true,42⟩,⟨19,[(false,true),(false,true)],false,42⟩,⟨19,[(false,true),(false,true)],true,42⟩]
def assignments20 : List Assignment := [⟨20,[(true,true),(true,true)],false,43⟩,⟨20,[(true,true),(true,true)],true,43⟩,⟨20,[(true,true),(false,false)],false,44⟩,⟨20,[(true,true),(false,false)],true,44⟩,⟨20,[(true,true),(true,false)],false,44⟩,⟨20,[(true,true),(true,false)],true,44⟩,⟨20,[(true,true),(false,true)],false,43⟩,⟨20,[(true,true),(false,true)],true,43⟩,⟨20,[(false,false),(true,true)],false,45⟩,⟨20,[(false,false),(true,true)],true,45⟩,⟨20,[(false,false),(false,false)],false,46⟩,⟨20,[(false,false),(false,false)],true,46⟩,⟨20,[(false,false),(true,false)],false,46⟩,⟨20,[(false,false),(true,false)],true,46⟩,⟨20,[(false,false),(false,true)],false,45⟩,⟨20,[(false,false),(false,true)],true,45⟩,⟨20,[(true,false),(true,true)],false,45⟩,⟨20,[(true,false),(true,true)],true,45⟩,⟨20,[(true,false),(false,false)],false,46⟩,⟨20,[(true,false),(false,false)],true,46⟩,⟨20,[(true,false),(true,false)],false,46⟩,⟨20,[(true,false),(true,false)],true,46⟩,⟨20,[(true,false),(false,true)],false,45⟩,⟨20,[(true,false),(false,true)],true,45⟩,⟨20,[(false,true),(true,true)],false,43⟩,⟨20,[(false,true),(true,true)],true,43⟩,⟨20,[(false,true),(false,false)],false,44⟩,⟨20,[(false,true),(false,false)],true,44⟩,⟨20,[(false,true),(true,false)],false,44⟩,⟨20,[(false,true),(true,false)],true,44⟩,⟨20,[(false,true),(false,true)],false,43⟩,⟨20,[(false,true),(false,true)],true,43⟩]
def assignments : List Assignment := [assignments0,assignments1,assignments2,assignments3,assignments4,assignments5,assignments6,assignments7,assignments8,assignments9,assignments10,assignments11,assignments12,assignments13,assignments14,assignments15,assignments16,assignments17,assignments18,assignments19,assignments20] |>.flatten
def matching (a : Assignment) : Bool :=
  systems (tables patterns[a.pattern]! a.modes a.subject) == allSystems[a.system]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate0 : assignments0.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate1 : assignments1.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate2 : assignments2.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate3 : assignments3.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate4 : assignments4.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate5 : assignments5.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate6 : assignments6.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate7 : assignments7.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate8 : assignments8.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate9 : assignments9.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate10 : assignments10.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate11 : assignments11.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate12 : assignments12.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate13 : assignments13.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate14 : assignments14.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate15 : assignments15.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate16 : assignments16.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate17 : assignments17.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate18 : assignments18.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate19 : assignments19.all matching = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate20 : assignments20.all matching = true := by decide +kernel
theorem all_certificates : assignments.all matching = true := by
  simp only [assignments,List.all_flatten,List.all_cons,List.all_nil,certificate0,certificate1,certificate2,certificate3,certificate4,certificate5,certificate6,certificate7,certificate8,certificate9,certificate10,certificate11,certificate12,certificate13,certificate14,certificate15,certificate16,certificate17,certificate18,certificate19,certificate20,Bool.and_self]
theorem source_system (a : Assignment) (ha : a∈assignments) :
    systems (tables patterns[a.pattern]! a.modes a.subject) = allSystems[a.system]! := by
  have h := (List.all_eq_true.mp all_certificates) a ha
  simpa [matching] using h
end InteractionTypology
