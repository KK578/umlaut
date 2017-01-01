# compm091-code

[![Build Status](https://travis-ci.com/KK578/compm091-code.svg?token=hs1VhKpTNLLpkBzhwkbp&branch=master)](https://travis-ci.com/KK578/compm091-code)
[![codecov](https://codecov.io/gh/KK578/compm091-code/branch/master/graph/badge.svg?token=IVRG99xGEK)](https://codecov.io/gh/KK578/compm091-code)

This project is part of a submission for the MEng Degree in Computer Science at UCL (University College London).



## Projects in this Repository

### UML-Annotator

Tool to annotate Visual Studio UML models.

### UML-Parser

Tool to convert UML models to a standard output for this project.

Output schema:
```md
{
	"className": {
		"name": "Name of class",
		"variables": {
			"variableName": {
				"name": "Name of variable",
				"visibility": "Public/Private",
				"type": "Type of variable"
			},
			/* ...Next variable */
		},

		"methods": {
			"methodName": {
				"name": "Name of method",
				"visibility": "Public/Private",
				"type: "Return type of method",
				"arguments": {
					"argument": "Type of argument",
					/* ...Next argument */
				},

				"preconditions": [
					{
						"id": "UUID for this precondition",
						"comparison": "Comparison name",
						"arguments": [
							"Name of variable or method argument or direct value",
							/* ...Next argument */
						]
					},
					/* ...Next precondition */
				],

				"postconditions": [
					{
						"id": "UUID for this postcondition",
						"comparison": "Comparison name",
						"arguments": [
							"Name of variable or method argument or direct value",
							/* ...Next argument */
						]
					},
					/* ...Next postcondition */
				]
			},
			/* ...Next method */
		}

	},
	/* ...Next class */
}
```

For list of comparison names, see [`comparisons.json`](./util/comparisons.json).

### Input-Generator

Tool to generate inputs for tests.

Extends schema of UML-Parser, with an additional `tests` array on each method:
```md
{
	"className": {
		...
		"methods": {
			"methodName": {
				...
				"tests": [
					{
						"condition": "Text identifying the meaning of the test",
						"arguments: {
							"argument": "Value of argument",
							/* ...Next argument */
						}
					},
					/* ...Next test */
				]
			},
			/* ...Next method */
		}

	},
	/* ...Next class */
}
```

In order to generate inputs, the design of this section is for submodules to handle specific types for the test.
Currently, only numerical logic is handled by the Input-Generator, though more is planned.

#### SMT-Solver

The SMT-Solver handles Boolean and Numerical Logic.
Implementation is handled via the conversion of the annotated constraints on the methods into Satisfiability Modulo Theorem, SMT.
Then by using Microsoft's [`z3`](https://github.com/Z3Prover/z3), the constraints are solved to generate values that satisfy the constraints.

### Test-Generator

Tool to take the UML model and inputs and generate the test suite.



## Installation

This is a project dependent on C# (For UML-Annotator) and Node.js (For UML-Parser, Input-Generator and Test-Generator).  
**This project also uses ES6 syntax, which requires `node` version `v6.0.0` at minimum.**

Please ensure that `node` and `npm` are installed and available in your PATH, to correctly run this project.  
Also check that `node --version` matches at least `v6.0.0`.

Node.js is available [here](https://nodejs.org) for all major OS platforms.

### Installing Locally

To install this project:

```bash
git clone https://github.com/KK578/compm091-code.git
cd compm091-code
npm install --production
npm link
```

This will setup the generator to work locally.



## Developing

### Dependencies

To develop the project, this project uses [`grunt`](https://gruntjs.com).

```bash
npm install -g grunt-cli
```

### Setup

```bash
git clone https://github.com/KK578/compm091-code.git
cd compm091-code
npm install
npm link
```

### Linting

Ensure changes adhere to the existing coding style.  
Check code changes with `grunt lint`.

### Unit tests

To test the project, this project uses `mocha`, and is setup via `grunt test`.  
For code coverage statistics, this project uses `istanbul`, and is setup via `grunt coverage`.

Continuous Integration builds is handled via Travis-CI, and is available [here](https://travis-ci.com/KK578/compm091-code).  
Code coverage information is handled via Codecov, and is available [here](https://codecov.io/gh/KK578/compm091-code).



## License

This project has been templated by [generator-kk578](https://github.com/KK578/generator-kk578).

[BSD-3 License](https://opensource.org/licenses/BSD-3-Clause)

Copyright (c) 2017, Kevin Kwan (KevinKwan@googlemail.com).  
All rights reserved.

*See [`LICENSE.md`](./LICENSE.md) for full license text.*
