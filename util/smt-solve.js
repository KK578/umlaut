const fs = require('fs');
const glob = require('glob');
const path = require('path');
const spawn = require('child_process').spawn;

function readFiles(dir, callback) {
	glob('**/*.smt2', { cwd: dir }, (err, files) => {
		if (err) {
			throw err;
		}

		const content = files.map((file) => {
			return fs.readFileSync(path.join(dir, file), 'utf-8');
		});

		callback(content);
	});
}

module.exports = {
	readFiles
};
