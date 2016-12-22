const glob = require('glob');
const path = require('path');
const fs = require('fs');
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

function promiseFsReadFile(filename) {
	return new Promise((resolve, reject) => {
		fs.readFile(filename, 'utf-8', (err, data) => {
			if (err) {
				reject(err);
			}
			else {
				resolve(data);
			}
		});
	});
}

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

function promiseRun(filename) {
	return promiseFsReadFile(filename).then(promiseSpawnZ3);
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
