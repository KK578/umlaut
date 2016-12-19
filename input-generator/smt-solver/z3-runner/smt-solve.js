const glob = require('glob');
const path = require('path');
const spawn = require('child_process').spawn;

const parser = require('./smt-parser.js');

function promiseReadFiles(dir) {
	return new Promise((resolve, reject) => {
		glob('**/*.smt2', { cwd: dir }, (err, files) => {
			if (err) {
				reject(err);
			}

			resolve(files);
		});
	});
}

function promiseSpawnZ3(filename) {
	return new Promise((resolve, reject) => {
		const z3 = spawn('z3', [filename]);
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
	});
}

function promiseHandleAllFiles(dir, files, result, index) {
	return new Promise((resolve, reject) => {
		if (index >= files.length) {
			resolve(result);
		}
		else {
			const filename = files[index];
			// Remove .smt2 from filename for method name.
			const methodName = filename.substring(0, filename.length - 5);
			const filepath = path.join(dir, filename);

			return promiseSpawnZ3(filepath).then((solved) => {
				result[methodName] = parser.parseZ3(solved);

				return promiseHandleAllFiles(dir, files, result, index + 1).then(resolve);
			}).catch(reject);
		}
	});
}

function solve(dir) {
	dir = path.resolve(dir);

	return promiseReadFiles(dir).then((smtFiles) => {
		return promiseHandleAllFiles(dir, smtFiles, {}, 0);
	});
}

module.exports = solve;
