const path = require('path');
const promises = require('../util/promises.js');

const umlToSmt = require('./uml-to-smt/index.js');
const solver = require('./z3-runner/index.js');

function promiseWriteAllFiles(dir, data, index) {
	return new Promise((resolve, reject) => {
		if (index >= data.smtCommands.length) {
			// All files are written.
			resolve();
		}
		else {
			const method = data.smtCommands[index];
			const filepath = path.join(dir, `${method.name}.smt2`);

			return promises.fsWriteFile(filepath, method.commands).then(() => {
				return promiseWriteAllFiles(dir, data, index + 1).then(resolve);
			}).catch((err) => {
				reject(err);
			});
		}
	});
}

function parseUml(uml) {
	return umlToSmt(uml);
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
