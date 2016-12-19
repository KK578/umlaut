const path = require('path');
const fs = require('fs');

const SmtClass = require('./uml-to-smt/class.js');
const solver = require('./z3-runner/smt-solve.js');

function promiseFsWriteFile(filepath, data) {
	return new Promise((resolve, reject) => {
		fs.writeFile(filepath, data, 'utf-8', (err) => {
			if (err) {
				reject(err);
			}
			else {
				resolve();
			}
		});
	});
}

function promiseWriteAllFiles(dir, data, index) {
	return new Promise((resolve, reject) => {
		if (index >= data.smtCommands.length) {
			// All files are written.
			resolve();
		}
		else {
			const method = data.smtCommands[index];
			const filepath = path.join(dir, `${method.name}.smt2`);

			return promiseFsWriteFile(filepath, method.commands).then(() => {
				return promiseWriteAllFiles(dir, data, index + 1).then(resolve);
			}).catch((err) => {
				reject(err);
			});
		}
	});
}

function parseUml(uml) {
	const smtClass = new SmtClass(uml);

	return smtClass;
}

function writeSmt(dir, smtClass) {
	const classPath = path.join(dir, `smt/${smtClass.name}/`);

	return promiseWriteAllFiles(classPath, smtClass, 0);
}

function solveSmt(dir) {
	return solver(dir);
}

module.exports = (uml) => {
	const parsedUml = parseUml(uml);
	const dir = 'build/';

	return writeSmt(dir, parsedUml).then(() => {
		return solveSmt(path.join(dir, 'smt/'));
	});
};
