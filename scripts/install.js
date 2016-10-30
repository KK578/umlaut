const root = process.cwd();
const fs = require('fs');
const path = require('path');
const spawn = require('child_process').spawnSync;

// get library path
const projects = [
	'smt-generator'
];

projects.map((project) => {
	const projectPath = path.join(root, project);
	const packageJson = path.join(projectPath, 'package.json');

	fs.stat(packageJson, (err, stats) => {
		if (err || stats.isDirectory()) {
			return;
		}

		console.log(`[npm Install] ${project}`);
		spawn('npm', ['install'], {
			env: process.env,
			cwd: projectPath,
			stdio: 'inherit'
		});
	});
});
