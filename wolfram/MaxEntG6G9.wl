(* Exact Wolfram calculations for the dissertation's MAX-G6--MAX-G9 results. *)

BeginPackage["MaxEntG6G9Calculations`"];

MaxEntG6G9Results::usage =
  "MaxEntG6G9Results[] returns the exact calculations for MAX-G6--MAX-G9.";

Begin["`Private`"];

ClearAll[basicSyllableCollapse];
basicSyllableCollapse[] :=
  Transpose[{{-1, 0, 0, -1}, {0, -1, -1, 0}}].{-1, -1};

ClearAll[vandermondeRatios];
vandermondeRatios[] := Table[
  With[{points = Array[x, n]},
    FullSimplify[
      Det[Table[points[[column]]^(row - 1), {row, n}, {column, n}]]/
        Product[
          points[[right]] - points[[left]],
          {left, 1, n - 1}, {right, left + 1, n}
        ]
    ]
  ],
  {n, 1, 7}
];

ClearAll[leibnizJetChecks];
leibnizJetChecks[] := Table[
  Expand[
    D[denominator[t] response[t], {t, order}] -
      Sum[
        Binomial[order, index]
          D[denominator[t], {t, index}]
          D[response[t], {t, order - index}],
        {index, 0, order}
      ]
  ] === 0,
  {order, 0, 10}
];

ClearAll[balancedContactChecks];
balancedContactChecks[] :=
  Table[
    Module[{y, polynomial, coefficients},
      polynomial = Expand[
        (-1)^reversals y (1 - y) (1 - 2 y)^contactOrder
          Product[2 (reversals + 1) y - index, {index, 1, reversals}]
      ];
      coefficients = Rest[CoefficientList[polynomial, y]];
      {
        Length[coefficients] === contactOrder + reversals + 2,
        FreeQ[coefficients, 0],
        And @@ Thread[Rest[Sign[coefficients]] == -Most[Sign[coefficients]]],
        FullSimplify[polynomial /. y -> 1] === 0,
        And @@ Table[
          index/(2 (reversals + 1)) < 1/2,
          {index, 1, reversals}
        ]
      }
    ],
    {contactOrder, 1, 8}, {reversals, 0, 8}
  ];

ClearAll[responseCounterexampleChecks];
responseCounterexampleChecks[] := Module[
  {z, lawOne, lawTwo, numerator},
  lawOne = (1 + z + z^2)/(1 + z + z^2 + z^3);
  lawTwo = (1 + z^2)/(1 + z^2 + z^3);
  numerator = Numerator[Together[lawOne - lawTwo]];
  <|
    "LawDifferenceNumeratorCoefficients" -> CoefficientList[Expand[numerator], z],
    "LawDifferenceNumeratorIsZ4" -> Expand[numerator - z^4] === 0,
    "PositiveDenominatorOnPositiveActivity" ->
      FullSimplify[
        (1 + z) (1 + z^2) (1 + z^2 + z^3) > 0,
        Assumptions -> z > 0
      ]
  |>
];

MaxEntG6G9Results[] := Module[
  {collapse, vandermonde, leibniz, contacts, response},
  collapse = basicSyllableCollapse[];
  vandermonde = vandermondeRatios[];
  leibniz = leibnizJetChecks[];
  contacts = balancedContactChecks[];
  response = responseCounterexampleChecks[];
  <|
    "BasicSyllableCollapseVector" -> collapse,
    "VandermondeExactRatiosN1ThroughN7" -> vandermonde,
    "LeibnizJetOrders0Through10AllExact" -> And @@ leibniz,
    "BalancedContactContractCount" -> Times @@ Take[Dimensions[contacts], 2],
    "BalancedContactAllExact" -> And @@ Flatten[contacts],
    "ResponseCounterexample" -> response
  |>
];

End[];
EndPackage[];
