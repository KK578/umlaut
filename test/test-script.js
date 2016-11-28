const path = require('path');

const umlParser = require('../uml-parser/index.js');
umlParser(path.join(__dirname, '../build/AnnotatedSimpleMath.uml'));

setTimeout(() => {
	// Take the annotated UML and create SMT files under 'build'.
	const SmtClass = require('../smt-generator/util/class.js');
	const data = require('../build/SimpleMath.json');
	const umlToSmt = new SmtClass(data.SimpleMath);
	umlToSmt.writeSMT(path.join(__dirname, '../build/'));

	setTimeout(() => {
		// Solves all SMT files to 'build/solved.json'.
		const z3Solver = require('../smt-generator/util/smt-solve.js');
		z3Solver.solve();
	}, 500);
}, 500);
