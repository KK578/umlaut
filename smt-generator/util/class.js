const SmtMethod = require('./method.js');
const path = require('path');
const fs = require('fs');

class SmtClass {
	constructor(classObject) {
		this.smtCommands = Object.keys(classObject.methods).map((m) => {
			const method = classObject.methods[m];
			const smtMethod = new SmtMethod(method);
			const commands = smtMethod.getCommands().join('\n');

			return {
				name: method.name,
				commands: commands
			};
		});
	}

	writeSMT(dir) {
		this.smtCommands.map((method) => {
			const fileName = path.join(dir, `${method.name}.smt2`);

			fs.writeFile(fileName, method.commands);
		});
	}
}

module.exports = SmtClass;
