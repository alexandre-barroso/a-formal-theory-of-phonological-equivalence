root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];
outdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];
If[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];
Get[FileNameJoin[{DirectoryName[$InputFileName], "interaction_typology_systems.wl"}]];
regions = Table[TimeConstrained[Reduce[Resolve[systems[[i]], Reals] && 0 <= lam <= 1, lam, Reals], 600, "TIMEOUT"], {i, 1, Length[systems]}];
res = <|"unique_systems" -> Length[systems], "assignments" -> Length[labels],
  "timeouts" -> Count[regions, "TIMEOUT"],
  "regions" -> Map[<|"pattern" -> #[[1]], "modes" -> #[[2]], "region" -> ToString[regions[[#[[3]]]], InputForm]|> &, labels]|>;
Export[FileNameJoin[{outdir, "interaction_typology_regions.json"}], res, "JSON"];
Print[res];
