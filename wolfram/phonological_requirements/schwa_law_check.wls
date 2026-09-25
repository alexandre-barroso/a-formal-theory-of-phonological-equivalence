root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];
outdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];
If[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];
word[cc_, cl_] := (1-cc) wCLU + cc wCCC + cl wCLASH - lam wS - wDEP;
clitic[cc_, cl_] := lam ((1-cc) wCLU + cc wCCC + cl wCLASH) + wMAX - wS;
res = <|"word_effect_ccc" -> Simplify[word[1, cl] - word[0, cl]] === wCCC-wCLU,
  "clitic_effect_ccc" -> Simplify[clitic[1, cl] - clitic[0, cl] == lam (wCCC-wCLU)],
  "word_effect_clash" -> Simplify[word[cc, 1] - word[cc, 0]] === wCLASH,
  "clitic_effect_clash" -> Simplify[clitic[cc, 1] - clitic[cc, 0]] === lam wCLASH,
  "common_ratio" -> Simplify[(clitic[1, cl] - clitic[0, cl])/(word[1, cl] - word[0, cl]) == (clitic[cc, 1] - clitic[cc, 0])/(word[cc, 1] - word[cc, 0]), wCCC != wCLU && wCLASH != 0]|>;
Export[FileNameJoin[{outdir, "schwa_law_check.json"}], res, "JSON"];
Print[res];
If[TrueQ[And @@ Values[res]], Exit[0], Exit[1]];
