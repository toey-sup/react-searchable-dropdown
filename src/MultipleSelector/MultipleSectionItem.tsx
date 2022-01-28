import { FC } from 'react';
import Typography from '@material-ui/core/Typography';
import Checkbox from '@material-ui/core/Checkbox';
import Tooltip from '@material-ui/core/Tooltip';

export interface MultipleChoice {
  label: string;
  used?: boolean;
  checked?: boolean;
  singleChoice?: boolean;
  id?: string;
  [key: string]: any;
}

export interface MultipleChoiceSection {
  choices: MultipleChoice[];
  sectionName?: string;
  sectionPrefix?: string;
}

export interface MultipleSectionItemProps {
  choice: MultipleChoice;
  checked: boolean;
  id?: string;
  className?: string;
  handleSelect: (choice: MultipleChoice, isCheck: boolean) => void;
}

const MultipleSectionItem: FC<MultipleSectionItemProps> = ({ choice, checked, id, className, handleSelect }) => {
  const usedStyle = 'text-gray-300 cursor-default';
  const defaultStyle = 'cursor-pointer hover:bg-gray-100';

  return (
    <Tooltip
      title={<Typography style={{ whiteSpace: 'pre-line' }}>{choice?.description}</Typography>}
      key={`${choice?.sectionPrefix || ''} ${choice?.label}`}
      enterDelay={300}
      leaveDelay={0}
      enterNextDelay={200}
      interactive
      placement="right-start"
      arrow
      disableHoverListener={!choice?.description}
    >
      <div
        key={choice?.fieldName || choice?.label}
        style={{ ...(choice?.used ? { color: 'gray' } : {}) }}
        className={`flex flex-row h-full pl-4 items-center ${choice?.used ? usedStyle : defaultStyle} ${className}`}
        onClick={() => {
          console.log(choice.used);
          if (!choice?.used) handleSelect(choice, !checked);
        }}
        id={`${id}${choice?.sectionName ? `-${choice?.sectionName}` : ''}-${choice?.label}`}
        aria-hidden="true"
      >
        {!choice.singleChoice && (
          <Checkbox
            color="primary"
            checked={checked}
            disableRipple
            disableFocusRipple
            disableTouchRipple
            style={{
              padding: 0,
              height: 'fit-content',
              marginRight: '0.5rem',
              cursor: choice?.used ? 'default' : 'pointer',
            }}
            size="small"
          />
        )}
        <Typography className="flex items-center pointer-events-none select-none">{choice.label}</Typography>
      </div>
    </Tooltip>
  );
};

export default MultipleSectionItem;
