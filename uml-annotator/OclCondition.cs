using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace UmlAnnotator
{
	public class OclCondition
	{
		public string Comparator { get; set; }
		private List<string> arguments;

		public OclCondition()
		{
			arguments = new List<string>();
		}

		public OclCondition(string condition)
		{
			string innerCondition = condition;
			if (innerCondition.StartsWith("("))
			{
				innerCondition = innerCondition.Substring(1, innerCondition.Length - 2);
			}

			string[] items = innerCondition.Split(' ');
			Comparator = items[0];

			arguments = new List<string>();
			for (int i = 1; i < items.Length; i++)
			{
				arguments.Add(items[i]);
			}
		}

		public void SetArguments(string argument)
		{
			arguments = new List<string>(Regex.Split(argument, "\r?\n"));
		}

		public string GetArgumentsString()
		{
			return String.Join("\r\n", arguments);
		}

		public override string ToString()
		{
			return String.Format("({0} {1})", Comparator, String.Join(" ", arguments));
		}
	}
}
