const fs = require('fs');
const glob = require('glob');
const path = require('path');
const spawn = require('child_process').spawn;

const parser = require('./smt-parser.js');

function readFiles(dir, callback) {
	glob('**/*.smt2', { cwd: dir }, (err, files) => {
		if (err) {
			throw err;
		}

		callback(files);
	});
}

function solveSmt(filename, callback) {
	const z3 = spawn('z3', [filename]);
	let output = '';

	z3.stdout.on('data', (data) => {
		output += data.toString('utf8');
	});

	z3.stderr.on('data', (data) => {
		output += data.toString('utf8');
	});

	z3.on('close', () => {
		callback(`${output}`);
	});
}

function solve(dir) {
	dir = path.resolve(dir);

	readFiles(dir, (smtFiles) => {
		let count = smtFiles.length;
		const result = {};

		smtFiles.map((smtFile) => {
			solveSmt(`${dir}/${smtFile}`, (solved) => {
				const methodName = smtFile.substring(0, smtFile.length - 5);
				result[methodName] = parser.parseZ3(solved);

				if (--count === 0) {
					const output = JSON.stringify(result, null, 2);
					fs.writeFile(path.join(dir, 'solved.json'), output, 'utf-8');
				}
			});
		});
	});
}

module.exports = {
	solve
};
