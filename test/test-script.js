const path = require('path');
const spawn = require('child_process').spawn;

console.log("Parse UML");
const umlParser = require('../uml-parser/index.js');
umlParser(path.join(__dirname, '../build/AnnotatedSimpleMath.uml'));

setTimeout(() => {
	console.log("Create SMT");
	// Take the annotated UML and create SMT files under 'build'.
	const SmtClass = require('../smt-generator/util/class.js');
	const data = require('../build/SimpleMath.json');
	const umlToSmt = new SmtClass(data.SimpleMath);
	umlToSmt.writeSMT(path.join(__dirname, '../build/'));

	setTimeout(() => {
		console.log("Solve SMT");
		// Solves all SMT files to 'build/solved.json'.
		const z3Solver = require('../smt-generator/util/smt-solve.js');
		z3Solver.solve();

		setTimeout(() => {
			console.log("Generate Test Suite");
			// Invoke generator.
			const yo = spawn('yo', ['umltotest:nunit', 'build/SimpleMath.json', 'build/solved.json']);

			yo.stdout.on('data', (data) => {
				console.log(data.toString('utf8'));
			});

			yo.stderr.on('data', (data) => {
				console.log(data.toString('utf8'));
			});
		}, 500);
	}, 500);
}, 500);