const spawn = require('child_process').spawn;

const parser = require('./smt-parser.js');

function promiseSpawnZ3(smtData) {
	return new Promise((resolve, reject) => {
		const z3 = spawn('z3', ['--in']);
		let output = '';

		z3.stdout.on('data', (data) => {
			output += data.toString('utf8');
		});

		z3.stderr.on('data', (data) => {
			output += data.toString('utf8');
		});

		z3.on('close', () => {
			// No code check as errors whilst z3 closes itself are not major errors.
			//  e.g. get-value may have failed to generate due to impossible conditions.
			resolve(output);
		});

		z3.on('error', (err) => {
			reject(err);
		});

		z3.stdin.write(smtData);
		z3.stdin.end();
	});
}

function promiseHandleSmt(smtCommands, result, index) {
	return new Promise((resolve, reject) => {
		if (index >= smtCommands.length) {
			resolve(result);
		}
		else {
			const smtMethod = smtCommands[index];
			const methodName = smtMethod.name;

			return promiseSpawnZ3(smtMethod.commands).then((solved) => {
				result[methodName] = parser.parseZ3(solved);

				return promiseHandleSmt(smtCommands, result, index + 1).then(resolve);
			}).catch(reject);
		}
	});
}

function solve(smt) {
	return promiseHandleSmt(smt.smtCommands, {}, 0);
}

module.exports = solve;
