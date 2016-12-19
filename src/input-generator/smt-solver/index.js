const path = require('path');
const fs = require('fs');

const SmtClass = require('./uml-to-smt/class.js');

function promiseFsWriteFile(filepath, data) {
	return new Promise((resolve, reject) => {
		fs.writeFile(filename, data, 'utf-8', (err) => {
			if (err) {
				reject(err);
			}
			else {
				resolve();
			}
		})
	});
}

function promiseWriteAllFiles(dir, data, index) {
	return new Promise((resolve, reject) => {
		if (index >= data.length) {
			// All files are written.
			resolve();
		}
		else {
			const method = data[index];
			const filePath = path.join(dir, `${method.name}.smt2`);

			return promiseFsWriteFile(filepath, method.commands).then(() => {
				return promiseWriteAllFiles(dir, data, index + 1);
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

function writeSmt(smtClass) {
	const classPath = path.join(dir, `smt/${smtClass.name}/`);

	return promiseWriteAllFiles(classPath, smtClass, 0);
}

module.exports = (uml) => {
	const parsedUml = parseUml(uml);

	return writeSmt(parsedUml);
};
