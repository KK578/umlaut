const spawn = require('child_process').spawn;

const parser = require('./value-parser.js');

function promiseSpawnZ3(smtData) {
	return new Promise((resolve, reject) => {
		const z3 = spawn('z3', ['--in']);
		let output = '';

		function storeData(data) {
			output += data.toString('utf-8');
		}

		// Grab from stderr as well in the case that the conditions were unsatisfiable.
		z3.stdout.on('data', storeData);
		z3.stderr.on('data', storeData);

		z3.on('close', () => {
			// No code check as errors whilst z3 closes itself are not major errors.
			//  e.g. get-value may have failed to generate due to impossible conditions.
			resolve(output);
		});
		z3.on('error', reject);

		// Write SMT-LIB2 commands into z3.
		z3.stdin.write(smtData);
		z3.stdin.end();
	});
}

function promiseHandleSmt(smt) {
	const smtCommands = smt.smtCommands;

	// Fold promise chain passing the result object along.
	// Pass initial value as uninitialised object to use as a hashmap.
	return smtCommands.reduce((previous, smtMethod) => {
		return previous.then((result) => {
			const methodName = smtMethod.name;

			// Run z3 and wait for data.
			return promiseSpawnZ3(smtMethod.commands).then((solved) => {
				// Error if method has already been parsed or been created twice.
				if (result[methodName] !== undefined) {
					throw new Error(`Method "${methodName}" already exists in Class "${smt.name}".`);
				}

				// Otherwise commit to hashmap and return to next smtMethod.
				result[methodName] = parser(solved);

				return result;
			});
		});
	}, Promise.resolve({}));
}

function solve(smt) {
	return promiseHandleSmt(smt);
}

module.exports = solve;
