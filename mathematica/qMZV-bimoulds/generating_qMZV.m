(* 
Generate values of combinatorial bi-multiple Eisenstein series and balanced qMZVs by computing the resp. generating series. The results are saved to dataDirRelCMES and dataDirRelBalanced from qMZV-bimoulds.m, respectively. 
The results can be loaded via CMES and balancedQMZV.
*)
Needs["DatabaseLink`"];

GenerateCMES::usage="GenerateCMES[d, maxDegree, readableExport, fileDest] computes the generating series of combinatorial bi-multiple Eisenstein series in depth d up to degree maxDegree and saves the results in the machine-readable WDX-format at fileDest. The results are Q-linear combinations of formal versions of the q-series g which can be expanded via ExpandSeriesG. The rational coefficients depend on the EDS solution used in betaCoeffReg. In particular, maxDegree must not exceed maxWeight-d. \nIf the (optional) argument readableExport is True, a human-readable version is additionally saved in a subfolder at fileDest. By default, readableExport is set to False. \nThe (relative) path fileDest is set to "<>ToString[dataDirRelCMES]<>" by default.";
GenerateCMES[d_Integer,maxDegree_Integer:10,readableExport_:False, fileDest_:dataDirRelCMES] := Module[{genSeriesCMES,coeffsLst,filenameReadable,dbFile,time},
	dbFile = "CMES_dep"<>ToString[d]<>".db";
	filenameReadable = FileNameJoin[{"readable","CMES_dep"<>ToString[d]<>".m"}];
	If[FileExistsQ[FileNameJoin[{fileDest,dbFile}]] || (readableExport && FileExistsQ[FileNameJoin[{fileDest,filenameReadable}]]),
		Print["Skipped computation. File already exists at ",fileDest],
		{time,genSeriesCMES} = Timing[bimouldCMES[MakeBiVariables[d],maxDegree,0]];
		coeffsLst = Reverse[CoefficientRules[genSeriesCMES, Variables[MakeBiVariables[d]],"DegreeLexicographic"]];
		Print["Finished computation of the generating series of combinatorial bi-multiple Eisenstein series in depth ",d," up to degree ",maxDegree," in ",time," seconds."];
		exportToDataBase[coeffsLst,FileNameJoin[{fileDest,dbFile}],False];
		If[readableExport,
			Export[FileNameJoin[{fileDest,filenameReadable}],coeffsLst,"Text"];
			Print["Saved coefficients also in a human-readable format at ",filenameReadable];
		];
	];
];

GenerateBalancedQMZV::usage="GenerateBalancedQMZV[d, maxDegree, readableExport, fileDest] computes the generating series of balanced multiple q-zeta values in depth d up to degree maxDegree and saves the results in the machine-readable WDX-format at fileDest. The results are Q-linear combinations of formal versions of the q-series g which can be expanded via ExpandSeriesG. The rational coefficients depend on the EDS solution used in betaCoeffReg. In particular, maxDegree must not exceed maxWeight-d. \nIf the (optional) argument readableExport is True, a human-readable version is additionally saved in a subfolder at fileDest. By default, readableExport is set to False. \nThe (relative) path fileDest is set to "<>ToString[dataDirRelBalanced]<>" by default.";
GenerateBalancedQMZV[d_Integer,maxDegree_Integer:10,readableExport_:False,  fileDest_String:dataDirRelBalanced] := Module[{genSeriesBalanced,coeffsLst, filenameReadable,dbFile,time},
	dbFile = "balanced_qMZV_dep"<>ToString[d]<>".db";
	filenameReadable = FileNameJoin[{"readable","balanced_qMZV_dep"<>ToString[d]<>".m"}];
	If[FileExistsQ[FileNameJoin[{fileDest,dbFile}]] || (readableExport && FileExistsQ[FileNameJoin[{fileDest,filenameReadable}]]),
		Print["Skipped computation. File already exists at ",fileDest],
		{time,genSeriesBalanced} = Timing[bimouldBalanced[MakeBiVariables[d],maxDegree,0]];
		coeffsLst = Reverse[CoefficientRules[genSeriesBalanced, Variables[MakeBiVariables[d]],"DegreeLexicographic"]];
		Print["Finished computation of the generating series of balanced multiple q-zeta values in depth ",d," up to degree ",maxDegree," in ",time," seconds."];
		exportToDataBase[coeffsLst,FileNameJoin[{fileDest,dbFile}],False];
		If[readableExport,
			Export[FileNameJoin[{fileDest,filenameReadable}],coeffsLst,"Text"];
			Print["Saved coefficients also in a human-readable format at ",filenameReadable];
		];
	];
];

(* auxiliary functions to write databases accordingly *)

exportToDataBase[coeffLst_List,dataDirRel_String,overwrite_:False] := Module[{conn,keyStr,valueStr, existsBool=FileExistsQ[dataDirRel], dataLst,time, chunkSize=20000, dataDirAbs = FileNameJoin[{Directory[],dataDirRel}]},
	Needs["DatabaseLink`"];
	time = AbsoluteTime[];
	conn=OpenSQLConnection[JDBC["SQLite",dataDirAbs]];
	If[existsBool,
		If[overwrite,SQLExecute[conn,"DROP TABLE IF EXISTS data"],
			Print["A database already exists at ",dataDirRel,". Consider calling exportToDataBase with optional argument overwrite = True. Note that this erases the content of the currently saved database."];
			Abort[];
		]
	];
	SQLExecute[conn,"
	   CREATE TABLE data (
	      key TEXT PRIMARY KEY,
	      value TEXT
	   )
	"];
	dataLst = Table[{ToString[First[entry]], ToString[Last[entry],InputForm]}, {entry,coeffLst}];
	SQLExecute[conn, "BEGIN TRANSACTION"];
	Do[SQLInsert[conn,
		"data",
		{"key", "value"},
		dataLst[[i;;Min[i+chunkSize-1, Length[dataLst]]]]
	],
	{i,1,Length[dataLst],chunkSize}];
	SQLExecute[conn, "COMMIT"];
	Print["Database created at ",dataDirRel," after ",AbsoluteTime[]-time," sec."];
	CloseSQLConnection[conn];
];