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

function promiseHandleSmtClass(smt) {
	const smtCommands = smt.smtCommands;

	const promises = smtCommands.map((smtMethod) => {
		const methodName = smtMethod.name;

		return promiseSpawnZ3(smtMethod.commands).then((solved) => {
			return {
				name: methodName,
				inputs: parser(solved)
			};
		});
	});

	return Promise.all(promises).then((resolved) => {
		const result = {};

		resolved.map((resolvedMethod) => {
			if (result[resolvedMethod.name] !== undefined) {
				throw new Error(`Method ${resolvedMethod.name} already exists.`);
			}

			result[resolvedMethod.name] = resolvedMethod.inputs;
		});

		return result;
	});
}

function promiseHandleSmt(smt) {
	const promises = Object.keys(smt).map((key) => {
		const smtClass = smt[key];
		const className = smtClass.name;

		return promiseHandleSmtClass(smtClass).then((inputs) => {
			return {
				name: className,
				inputs: inputs
			};
		});
	});

	return Promise.all(promises).then((resolved) => {
		const result = {};

		resolved.map((resolvedClass) => {
			if (result[resolvedClass.name] !== undefined) {
				throw new Error(`Class ${resolvedClass.name} already exists.`);
			}

			result[resolvedClass.name] = resolvedClass.inputs;
		});

		return result;
	});
}

function solve(smt) {
	return promiseHandleSmt(smt);
}

module.exports = solve;
