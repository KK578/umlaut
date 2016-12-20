const path = require('path');
// const spawn = require('child_process').spawn;

const umlParser = require('../../uml-parser/index.js');
const inputGenerator = require('../../input-generator/index.js');

function stringify(data) {
	return JSON.stringify(data, null, 2);
};

let parsedData;
let solvedData;

return umlParser(path.join(__dirname, '../../build/AnnotatedSimpleMath.uml')).then((data) => {
	console.log('Parsed UML');
	parsedData = data;
	console.log(stringify(parsedData));

	return inputGenerator.smtSolve(parsedData.SimpleMath);
}).then((data) => {
	console.log('Created SMT');
	solvedData = data;
	console.log(stringify(solvedData));
}).catch((err) => {
	console.error(err);
});

// setTimeout(() => {
// 	console.log('Generate Test Suite');

// 	// Invoke generator.
// 	const yo = spawn('yo', ['model-driven-testing:nunit', 'build/uml/', 'build/smt/']);

// 	yo.stdout.on('data', (data) => {
// 		console.log(data.toString('utf8'));
// 	});

// 	yo.stderr.on('data', (data) => {
// 		console.log(data.toString('utf8'));
// 	});
// }, 500);
