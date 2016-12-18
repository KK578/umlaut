const path = require('path');
const spawn = require('child_process').spawn;
const umlParser = require('../src/uml-parser/index.js');

console.log('Parse UML');
umlParser(path.join(__dirname, '../build/AnnotatedSimpleMath.uml'));

setTimeout(() => {
	console.log('Create SMT');

	// Take the annotated UML and create SMT files under 'build'.
	const smtGenerator = require('../src/smt-generator/index.js');
	const data = require('../build/uml/SimpleMath.json');
	const smt = smtGenerator.parseUml(data);

	smtGenerator.write(smt, path.join(__dirname, '../build/'));

	setTimeout(() => {
		console.log('Solve SMT');

		// Solves all SMT files to 'build/solved.json'.
		const z3Solver = require('../src/smt-generator/util/smt-solve.js');

		z3Solver.solve(path.join(__dirname, '../build/smt/SimpleMath/'));

		setTimeout(() => {
			console.log('Generate Test Suite');

			// Invoke generator.
			const yo = spawn('yo', ['model-driven-testing:nunit', 'build/uml/', 'build/smt/']);

			yo.stdout.on('data', (data) => {
				console.log(data.toString('utf8'));
			});

			yo.stderr.on('data', (data) => {
				console.log(data.toString('utf8'));
			});
		}, 500);
	}, 500);
}, 500);
