const path = require('path');
const fs = require('fs');

const SmtClass = require('./smt-solver/uml-to-smt/class.js');

function parseUml(uml) {
	const smtClass = new SmtClass(uml);

	return smtClass;
}

function write(smtClass, dir) {
	const classPath = path.join(dir, `smt/${smtClass.name}/`);

	smtClass.smtCommands.map((method) => {
		const filePath = path.join(classPath, `${method.name}.smt2`);

		fs.writeFile(filePath, method.commands);
	});
}

module.exports = {
	smtSolve: require('./smt-solver/index.js'),
	write
};
