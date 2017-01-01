# compm091-code

[![Build Status](https://travis-ci.com/KK578/compm091-code.svg?token=hs1VhKpTNLLpkBzhwkbp&branch=master)](https://travis-ci.com/KK578/compm091-code)
[![codecov](https://codecov.io/gh/KK578/compm091-code/branch/master/graph/badge.svg?token=IVRG99xGEK)](https://codecov.io/gh/KK578/compm091-code)

This project is part of a submission for the MEng Degree in Computer Science at UCL (University College London).

## Projects in this Repository

### UML-Annotator

Tool to annotate Visual Studio UML models.

### UML-Parser

Tool to convert UML models to a standard output for this project.

### Input-Generator

Tool to generate inputs for tests.

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
