(* ::Package:: *)

(* Wolfram Language Package *)

(* Created by the Wolfram Workbench May, 2015 
   Author: Paco Jain (pacojain@gmail.com)
*)

BeginPackage["GeometricAlgebra`"]
(* Exported symbols added here with SymbolName::usage *)
$DefaultAlgebra
$ShowGeometricProduct
DeclareAlgebra
ClearAlgebra
AssociatedAlgebra
BasisBlades
Dimension
GeometricProduct
DeclareMultivector
ClearMultivector
GradeProject

Begin["`Private`"]
(* Implementation of the package *)
ClearAll["GeometricAlgebra`*"]
$ShowGeometricProduct = True
$Pre = .
$Post = .

(* helper functions ---------------------------------------------------------------*)
ClearAll[declareBasisBlade]
SetAttributes[declareBasisBlade, HoldAll]
declareBasisBlade[symbolList_List, colorHue_: 0.4 ] := Module[
	{
		color, symbolBoxExpression,
		bladeSym = Symbol[StringJoin @@ SymbolName /@ symbolList]
	},
	color = Hue[colorHue, 0.5, 0.6];
	symbolBoxExpression = StyleBox[RowBox@Most@Flatten[{SymbolName[#], "\[Wedge]"} & /@ symbolList], FontWeight -> "Fat", color];
	(# /: MakeBoxes[#, StandardForm] := symbolBoxExpression) &@bladeSym;
	Protect[Evaluate[bladeSym]];
	bladeSym
]
	
ClearAll[bladeSetSignature]
bladeSetSignature[bladeSet_List, symbolList_List] := Module[
	{
		concatedSymbolList = bladeSet~Join~Fold[DeleteCases, symbolList, bladeSet],
		positionOrdering
	},
	If[Length[bladeSet] === 1, Return[1]];
	positionOrdering = Position[symbolList, #] & /@ concatedSymbolList // Flatten;
	Signature[positionOrdering]
]
bladeSetSignature[bladeSet_List, algebra_String] := bladeSetSignature[bladeSet, BasisBlades[algebra, 1]]

ClearAll[orderBladeSet]
orderBladeSet[bladeSet_List, symbolList_List] := Module[
	{
		i, sig, pos, sortList, tempList = bladeSet
	},
	sortList = Symbol /@ Flatten[Cases[SymbolName /@ bladeSet, #] & /@ SymbolName /@ symbolList];
	sig = 1;
	For[i = 1, i <= Length[tempList], i++,
		If[tempList[[i]] === sortList[[i]], Continue[]];
		pos = Select[
		Position[tempList, sortList[[i]]][[All, 1]], # > i &] // First;
		tempList = ReplacePart[tempList, {pos -> tempList[[i]], i -> sortList[[i]]}];
		sig = -sig
	];
	tempList = If[Length[#]~Mod~2 === 0, {}, #[[1]]] & /@ Gather[tempList] // Flatten;
	If[bladeSetSignature[tempList, symbolList] === -1, tempList = ReplacePart[tempList, {-2 -> tempList[[-1]], -1 -> tempList[[-2]]}]; sig = -sig];
	Join[{sig}, tempList]
]
orderBladeSet[first_, algebra_String] := 
orderBladeSet[first, BasisBlades[algebra, 1]]

ClearAll[decomposeBlade, recomposeBlade]
decomposeBlade[sym_Symbol, algebra_String: $DefaultAlgebra] := Symbol /@ StringCases[SymbolName[sym], Alternatives @@ SymbolName /@ BasisBlades[algebra, 1]]
recomposeBlade[bladeSet_List, algebra_String: $DefaultAlgebra] := First[bladeSet] If[# =!= "", Symbol[#], 1] &[ StringJoin[SymbolName /@ Rest[bladeSet]] ]

(* Main functions *)
ClearAll[DeclareAlgebra]
DeclareAlgebra::notsym = "Argument `1` is expected to be an unassigned symbol. Try clearing and unprotecting all variables prior to use.";
DeclareAlgebra::algex = "Algebra `1` already has associated definitions. Try renaming, or evaluate ClearAlgebra[`1`] prior to use.";
DeclareAlgebra[algName_String, symbolList_List] := Module[
	{
		bladeSets, bladeList = {}, bladeSyms, n
	},
	If[ ! FreeQ[DownValues /@ {AssociatedAlgebra, Dimension, BasisBlades} // Flatten, algName], Message[DeclareAlgebra::algex, algName // FullForm]; Return[$Failed, Module] ];
	If[ Quiet[Head[#] =!= Symbol] || MemberQ[Attributes[#], Protected], Message[DeclareAlgebra::notsym, #, Position[symbolList, #][[1]]]; Return[$Failed, Module] ] & /@ symbolList;
	bladeSets = Rest[orderBladeSet[#, symbolList]] & /@ (Subsets[symbolList] // Rest) // GatherBy[#, Length] &;
	n = Length[bladeSets];
	For[i = 1, i <= n, i++,
		bladeSyms = declareBasisBlade[#, i/n] & /@ bladeSets[[i]];
		AppendTo[bladeList, bladeSyms];
		BasisBlades[algName, i] = bladeSyms;
	];
	Dimension[algName] = Length[symbolList];
	BasisBlades[algName] = BasisBlades[algName, #] & /@ Table[i, {i, 1, Dimension[algName]}] // Flatten;
	(AssociatedAlgebra[#] = algName) & /@ BasisBlades[algName];
	$DefaultAlgebra = algName;
	bladeList
	]
DeclareAlgebra[algName_String, baseSym_String, dimension_Integer] := Module[
	{
		symbolList = Symbol /@ (StringJoin[baseSym, #] & /@ Table[ToString[i], {i, 1, dimension}])
	},
	If[ FreeQ[symbolList, Symbol], DeclareAlgebra[algName, symbolList], $Failed]
]

ClearAll[ClearAlgebra]
ClearAlgebra::notalg = "String `1` does not appear to be associated with an existing algebra. No action was taken.";
ClearAlgebra[algName_String] := Module[
	{
		bladeSyms
	},
	If[FreeQ[DownValues[AssociatedAlgebra], algName], Message[ClearAlgebra::notalg, algName // FullForm]; Return[]];
	Unset /@ Cases[DownValues[AssociatedAlgebra], _?(! FreeQ[#, algName] &)][[All, 1]];
	If[FreeQ[DownValues[Dimension], algName], Return[]];
	bladeSyms = BasisBlades[algName, #] & /@ Table[i, {i, 1, Dimension[algName]}] // Flatten;
	Unprotect /@ bladeSyms;
	ClearAll /@ bladeSyms;
	Unset /@ Cases[DownValues[Dimension], _?(! FreeQ[#, algName] &)][[All, 1]];
	Unset /@ Cases[DownValues[BasisBlades], _?(! FreeQ[#, algName] &)][[All, 1]];
]

ClearAll[DeclareMultivector, ClearMultivector]
SetAttributes[DeclareMultivector, HoldFirst]
SetAttributes[ClearMultivector, HoldFirst]
ClearMultivector::clrbas = "Symbol `1` is in the basis of algebra `2`.  Use ClearAlgebra[`2`] to free this and other basis symbols.";
DeclareMultivector[sym_Symbol, algebra_String: $DefaultAlgebra] := Module[
	{},
	ClearAll[sym];
	AssociatedAlgebra[sym] = algebra; 
	sym /: MakeBoxes[sym, StandardForm] := StyleBox[SymbolName[sym], Bold];
]
ClearMultivector[sym_Symbol, algebra_String: $DefaultAlgebra] := Module[
	{},
	If[! FreeQ[DownValues[BasisBlades], sym], Message[ClearMultivector::clrbas, sym, algebra // FullForm]; Return[]];
	ClearAll[sym];
	AssociatedAlgebra[sym] =.;
]

GradeProject /: MakeBoxes[GradeProject[a_, n_], StandardForm] := RowBox[{"<", ToBoxes[a], ",", ToBoxes[n], ">"}]
GradeProject /: MakeBoxes[GradeProject[a_, 0], StandardForm] := RowBox[{"<\[NegativeThickSpace]", ToBoxes[a], "\[NegativeThinSpace]>"}]
GradeProject[a_] := GradeProject[a, 0]

(* Interpret times as geometric product *)
ClearAll[GeometricProduct]
ClearAttributes[GeometricProduct, All]
GeometricProduct[s_] := s
GeometricProduct[] := 1
GeometricProduct[first___, Verbatim[Plus][args__], val_, rest___] := Plus @@ (GeometricProduct[first, #, val, rest] & /@ {args})
GeometricProduct[first___, val_, Verbatim[Plus][args__], rest___] := Plus @@ (GeometricProduct[first, val, #, rest] & /@ {args})
GeometricProduct[Times[a_?(AssociatedAlgebra[#] =!= $DefaultAlgebra &), rest__], b_] := Times[a, GeometricProduct[rest, b]]
GeometricProduct[a_, Times[b_?(AssociatedAlgebra[#] =!= $DefaultAlgebra &), rest__]] := Times[b, GeometricProduct[a, rest]]
GeometricProduct[first___, Times[mid1___, a_, b_, mid2___], rest___] :=
GeometricProduct[first, Times[mid1, a], Times[b, mid2], rest]
(*GeometricProduct[first___,a_?(AtomQ[#]&&AssociatedAlgebra[#]=!=$DefaultAlgebra&),rest___]:=Times[a,GeometricProduct[first,rest]]*)
GeometricProduct[first___, a_?(FreeQ[#, _?(AssociatedAlgebra[#] === $DefaultAlgebra &)] &), rest___] := Times[a, GeometricProduct[first, rest]]

ClearAll[myPre];
SetAttributes[myPre, HoldAll];
myPre[input_] := Module[
	{result},
	ClearAttributes[Times, Orderless];
	result = (Hold[input] /. HoldPattern[Times[args___]] :> GeometricProduct[args]) // ReleaseHold;
	SetAttributes[Times, Orderless];
	result
]; 
$Pre := myPre;

(* Typeset GeometricProduct (and control visibility via $ShowGeometricProduct) *)
GeometricProduct /: MakeBoxes[GeometricProduct[args__], StandardForm] := If[
	$ShowGeometricProduct == True,
	RowBox[{"GeometricProduct", "[", RowBox[Riffle[MakeBoxes /@ {args}, ","]], "]"}], 
	RowBox[Riffle[MakeBoxes /@ {args}, " "]]
]

End[]
EndPackage[]